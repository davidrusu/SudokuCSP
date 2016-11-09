import Control.Monad (replicateM, mapM_, forever)
import Data.List (tails, find, delete, sortBy, foldl')
import Data.Time.Clock.POSIX
import Debug.Trace (trace);
import qualified Data.Map as Map
data Puzzle = Puzzle Int [[Int]] deriving (Eq)
type Var = (Int, Int) -- index into grid
type Domain = [Int]

timeInMicros :: IO Integer
timeInMicros = do
  t <- getPOSIXTime
  let micros = round $ (t * 1000000)
  pure micros


timeInMillis :: IO Integer
timeInMillis = (`div` 1000) <$> timeInMicros

data Rule = Neq Var Var | Const Var Int deriving (Eq)

type Constraints = Map.Map (Var, Var) [Rule]

data CSP = CSP { vars :: [Var]
               , constraints :: Constraints
               , assigns :: Map.Map Var Int
               , domains :: Map.Map Var Domain
               , puzzle :: Puzzle
               } deriving (Eq)

instance Show Rule where
  show (Neq a b) = (show a) ++ "/=" ++ (show b)
  show (Const a b) = (show a) ++ ":=" ++ (show b)

normArc :: Var -> Var -> (Var, Var)
normArc v1 v2 = if v1 < v2 then (v1, v2) else (v2, v1)

neqRule :: Constraints -> Var -> Var -> Constraints
neqRule rules var1 var2 = Map.insertWith (++) (normArc var1 var2) [Neq var1 var2] rules

neqRulePairs :: Constraints -> Var -> [Var] -> Constraints
neqRulePairs rules var1 var2s = foldl' (\rs var2 -> neqRule rs var1 var2) rules var2s

rowConstraint :: Int -> Int -> Constraints
rowConstraint n r =
  foldl' genConstraintsForColumn Map.empty [0..n-1]
  where
    genConstraintsForColumn :: Constraints -> Int -> Constraints
    genConstraintsForColumn rules c = neqRulePairs rules var1 var2s
      where
        var1 = (r, c)
        var2s = tail $ zip (repeat r) [c..n-1] -- tail because we already have (r,c) in var1

squareConstraint :: Int -> Int -> Int -> Constraints
squareConstraint n rOffset cOffset = constraints
  where nD3 = n `div` 3
        coords :: [Var]
        coords = concatMap (\r-> map (\c-> (r + rOffset, c + cOffset)) [0..(nD3-1)]) [0..(nD3-1)]
        constraints :: Constraints
        constraints = foldl' (\rules v1 -> neqRulePairs rules v1 (filter (/= v1) coords)) Map.empty coords

genConstraints :: Puzzle -> Constraints
genConstraints (Puzzle n grid) = Map.unionsWith (++) [ rowConstraints
                                                     , colConstraints
                                                     , squareConstraints
                                                     , constConstraints
                                                     ]
  where
    rowConstraints :: Constraints
    rowConstraints = foldl' (\rules row -> Map.unionWith (++) rules (rowConstraint n row)) Map.empty [0..n-1]
    colConstraints :: Constraints
    colConstraints = Map.fromList $
      map (\(((rv1, cv1), (rv2, cv2)), rules) ->
             (((cv1, rv1), (cv2, rv2)), map (\(Neq (r, c) (r2, c2)) -> Neq (c, r) (c2, r2)) rules)) $
      Map.toList rowConstraints
    squareConstraints :: Constraints
    squareConstraints = Map.unionsWith (++) [ squareConstraint n 0 0
                                            , squareConstraint n 0 nD3
                                            , squareConstraint n 0 (2 * nD3)
                                            , squareConstraint n nD3 0
                                            , squareConstraint n nD3 nD3
                                            , squareConstraint n nD3 (2 * nD3)
                                            , squareConstraint n (2 * nD3) 0
                                            , squareConstraint n (2 * nD3) nD3
                                            , squareConstraint n (2 * nD3) (2 * nD3)
                                            ]
    constConstraints :: Constraints
    constConstraints = Map.fromList $
          map (\(r, c, v) -> (((r, c), (r,c)), [Const (r, c) v])) (
            filter (\(r, c, v) -> v /= 0) (
                concatMap (\(r, row) -> map (\(c, v) -> (r, c, v)) (zip [0..] row)) (zip [0..] grid)))
    nD3 = n `div` 3

variables :: Int -> [Var]
variables n = genVars [0..(n-1)]
  where genVars [] = []
        genVars (r:rs) = (map (\r2 -> (r, r2)) [0..(n-1)]) ++ genVars rs

readInt :: String -> Int
readInt = read

readRow :: String -> [Int]
readRow line = map (\c -> readInt (c:"")) line

parseRow :: IO [Int]
parseRow = do
  line <- getLine
  pure $ readRow line

parsePuzzle :: IO Puzzle
parsePuzzle = do
  n <- (getLine >>= (pure . read)) :: IO Int
  grid <- replicateM n parseRow
  pure (Puzzle n grid)

showRow :: [Int] -> String
showRow [] = "\n"
showRow (n:ns) = (if n == 0 then "  " else show n ++ " ") ++ showRow ns

showPuzzle :: CSP -> String
showPuzzle csp =
  let
    (CSP {puzzle=Puzzle n grid}) = fillIn csp
    header = (show n) ++ " x " ++ (show n)
  in 
  "\n" ++
  (replicate (n - ((length header) `div` 2)) ' ' ) ++ header ++
  "\n" ++
  (replicate (n * 2) '=') ++
  "\n" ++
  (concatMap showRow grid)

buildCSP :: Puzzle -> CSP
buildCSP puzzle@(Puzzle n grid) = CSP { vars = vars
                                      , constraints = genConstraints puzzle
                                      , assigns = Map.fromList $ map (\v -> (v, -1)) vars
                                      , domains = Map.fromList $ map (\v -> (v, [1..n])) vars
                                      , puzzle = puzzle
                                      }
  where vars = variables n

replace :: (a -> Bool) -> (a -> a) -> [a] -> [a]
replace _ _ [] = []
replace f g (x:xs) = if f x then (g x) : xs else x : (replace f g xs)

update :: Int -> (a -> a) -> [a] -> [a]
update _ _ [] = []
update 0 f (x:xs) = (f x) : xs
update n f (x:xs) | n < 0 = undefined
               | otherwise = x : (update (n-1) f xs)

restrictDomainConst :: CSP -> Var -> Int -> CSP
restrictDomainConst csp var val =
  csp { domains = Map.update (const $ Just [val]) var (domains csp)
      , assigns = Map.update (const $ Just val) var (assigns csp) }


restrictDomainNeq :: CSP -> Var -> Var -> CSP
restrictDomainNeq csp var1 var2 =
  case Map.lookup var1 $ domains csp of
       Just dom1 -> csp {
         domains = Map.update (\dom2 -> Just $ restrict dom1 dom2) var2 (domains csp) }
       Nothing -> undefined
  where neqExists x xs = any (/= x) xs
        restrict :: [Int] -> [Int] -> [Int]
        restrict dom1 dom2 = foldl' (\d v-> if neqExists v dom1 then d else delete v d ) dom2 dom2
                                  

nodeConsistant :: CSP -> CSP
nodeConsistant csp = nodeConsistantCSP { constraints = binary }
  where unary = filter (\c -> case c of
                              Const _ _ -> True
                              _         -> False) (concatMap snd $ Map.toList $ constraints csp)
        binary = Map.filterWithKey (\(v1, v2) _ -> v1 /= v2) $ constraints csp
        nodeConsistantCSP = foldl' (\csp (Const var val) -> restrictDomainConst csp var val) csp unary

allArcs :: CSP -> Var -> [(Var, Var)]
allArcs csp v = filter isValidArc arcs
  where
    otherVars = filter (/= v) $ vars csp
    arcs = (zip (repeat v) otherVars)
    isValidArc arc = Map.member arc $ constraints csp

anyEmptyDomains csp = (Map.size $ Map.filter (\dom -> length dom == 0) (domains csp)) > 0

assignConstDomains csp =
  foldl' (\csp var->
            let dom = getDomain csp var in 
            if length dom == 1
                     then
                       csp { assigns = Map.update
                                         (const $ Just (head dom))
                                         var
                                         (assigns csp)
                           }
                     else
                       csp
         )
    csp (vars csp)

ac3 :: CSP -> [(Var, Var)] -> Maybe CSP
ac3 csp [] = Just csp
ac3 csp arcs = if anyEmptyDomains csp
               then Nothing
               else ac3 newCSP newArcs
  where (newCSP, newArcs) = foldl' (\(csp, queue) (var1, var2) ->
                                      let restrictedCSP = restrictDomainNeq csp var1 var2
                                          assignedCSP = case getDomain restrictedCSP var2 of
                                                          (val:[]) ->
                                                            restrictedCSP { assigns = Map.update
                                                                                        (const $ Just val)
                                                                                        var2
                                                                                        (assigns restrictedCSP)
                                                                          }
                                                          _ ->
                                                            restrictedCSP 
                                      in
                                      if (getDomain assignedCSP var2) /= (getDomain csp var2)
                                      then (assignedCSP, queue ++ (allArcs assignedCSP var2))
                                      else (assignedCSP, queue)) (csp, []) arcs

fillIn :: CSP -> CSP
fillIn csp = csp { puzzle = Puzzle n assignedGrid }
  where
    certain = Map.filter (\dom -> length dom == 1) $ domains csp
    initGrid = replicate n $ replicate n 0
    assignedGrid =
      Map.foldWithKey
        (\(r, c) val grid -> update r (update c (const val)) grid)
        initGrid
        (Map.filter (> 0) $ assigns csp)
    -- filledGrid = foldl (\grid ((r, c), [val]) -> update r (update c (const val)) grid) assignedGrid certain
    Puzzle n _ = puzzle csp

getDomain :: CSP -> Var -> Domain
getDomain csp var =
  case Map.lookup var $ domains csp of
     Just d -> d
     Nothing -> undefined
  
getConstraints :: CSP -> Var -> Var -> [Rule]
getConstraints csp v1 v2 = rs
  where
    cs = constraints csp
    rs = case Map.lookup (normArc v1 v2) cs of
           Just rules -> rules
           Nothing    -> []

constraintsHold :: Map.Map Var Int -> [Rule] -> Bool
constraintsHold _ [] = True
constraintsHold vars ((Neq v1 v2):rs) =
  case (Map.lookup v1 vars, Map.lookup v2 vars) of
    (Just val1, Just val2) ->
      val1 > 0 && val2 > 0 && val1 /= val2 && (constraintsHold vars rs)
    _ ->
      error "blah"

constraintsHold vars ((Const var val):rs) =
  case Map.lookup var vars of
    Just val1 ->
      val1 == val  && (constraintsHold vars rs)
    _ ->
      undefined

testAssign :: CSP -> (Var, Int) -> Bool
testAssign csp (var, assign) = constraintsHold updatedAssigns relaventConstraints
  where
    updatedAssigns = assigns $ restrictDomainConst csp var assign
    otherAssigns :: [Var]
    otherAssigns = Map.keys $ Map.filter (> 0) $ assigns csp
    relaventConstraints =
      concatMap (getConstraints csp var) otherAssigns

selectUnassignedVar csp =
  fst $ head $
  sortBy (\(v1,_) (v2,_) ->
            compare (length (getDomain csp v1)) (length (getDomain csp v2))) $
  Map.toList $ Map.filter (<= 0) (assigns csp)

assignsComplete csp = (Map.size $ Map.filter (<= 0) (assigns csp)) == 0

solve :: CSP -> Maybe CSP
solve csp = if assignsComplete csp  then Just csp else
              if anyEmptyDomains csp then Nothing else
                case dropWhile (== Nothing) potentialSolutions of
                  [] -> Nothing
                  (Just csp):_ -> Just csp
  where
    var = selectUnassignedVar csp
    consistantValues = filter (\val -> testAssign csp (var, val)) (getDomain csp var)
    arcs = allArcs csp var
    potentialSolutions = map (\val ->
                                (ac3 (restrictDomainConst csp var val) arcs) >>= solve ) (getDomain csp var)

everyArc csp = concatMap (\var -> allArcs csp var) $ vars csp

main = forever $ do
  tStart <- timeInMillis
  
  puzzle <- parsePuzzle
  let csp = buildCSP puzzle
  let nodeCsp = nodeConsistant csp
  let ac3Csp = ac3 nodeCsp $ everyArc nodeCsp
  case ac3Csp of
    Nothing -> putStrLn "Failed at ac3"
    Just csp -> putStrLn $ showPuzzle csp
  case ac3Csp >>= solve of
    Just csp -> putStrLn $ showPuzzle csp
    Nothing -> putStrLn "Failed to solve"
  
  tFinish <- timeInMillis
  putStrLn ("Time solve: " ++ (show (tFinish - tStart)) ++ "millis")
