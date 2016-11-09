import Control.Monad (replicateM, mapM_, forever)
import Data.List (tails, find, delete, sortBy, foldl')
import Data.Time.Clock.POSIX
import Debug.Trace (trace);
import qualified Data.Map.Strict as Map
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
genConstraints (Puzzle n grid) =
  Map.unionsWith (++) [rowConstraints, colConstraints, squareConstraints, constConstraints]
  where
    rowConstraints = foldl' (\rules row -> Map.unionWith (++) rules (rowConstraint n row)) Map.empty [0..n-1]
    colConstraints = Map.fromList $
      map (\(((rv1, cv1), (rv2, cv2)), rules) ->
             (((cv1, rv1), (cv2, rv2)), map (\(Neq (r, c) (r2, c2)) -> Neq (c, r) (c2, r2)) rules)) $
      Map.toList rowConstraints
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
showPuzzle csp = unlines $ [ (replicate (n - ((length header) `div` 2)) ' ' ) ++ header
                           , (replicate (n * 2) '=')
                           , (concatMap showRow grid)
                           ]
  where Puzzle n grid = puzzle $ fillIn csp
        header = (show n) ++ " x " ++ (show n)

buildCSP :: Puzzle -> CSP
buildCSP puzzle@(Puzzle n grid) = CSP { vars = variables n
                                      , constraints = genConstraints puzzle
                                      , assigns = Map.empty
                                      , domains = Map.fromList $ map (\v -> (v, [1..n])) vars
                                      , puzzle = puzzle
                                      }

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
  csp { domains = Map.insert var [val] (domains csp)
      , assigns = Map.insert var val (assigns csp) }


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

unassignedArcs :: CSP -> Var -> [(Var, Var)]
unassignedArcs csp v = filter isValidArc arcs
  where
    otherVars = filter (\var -> Map.notMember var (assigns csp)) $ vars csp
    arcs = zip (repeat v) otherVars
    isValidArc (v1, v2) = Map.member (normArc v1 v2) $ constraints csp

anyEmptyDomains csp = (Map.size $ Map.filter (\dom -> length dom == 0) (domains csp)) > 0

ac3' :: CSP -> [(Var, Var)] -> Maybe CSP
ac3' csp [] = trace (show $ 1 + length arcs) $ Just csp
ac3' csp ((var1, var2):arcs) =
  trace (show $ 1 + length arcs) $ 
  if anyEmptyDomains csp
  then Nothing
  else ac3' restrictedCSP newArcs
    where restrictedCSP = restrictDomainNeq csp var1 var2
          newArcs = if (getDomain restrictedCSP var2) /= (getDomain csp var2)
                    then (unassignedArcs restrictedCSP var2) ++ arcs
                    else arcs

ac3 :: CSP -> [(Var, Var)] -> Maybe CSP
ac3 csp [] = Just csp
ac3 csp arcs = if anyEmptyDomains csp
               then Nothing
               else ac3 newCSP newArcs
  where (newCSP, newArcs) = foldl' (\(csp, queue) (var1, var2) ->
                                      let restrictedCSP = restrictDomainNeq csp var1 var2 in
                                      if (getDomain restrictedCSP var2) /= (getDomain csp var2)
                                      then (restrictedCSP, queue ++ (unassignedArcs restrictedCSP var2))
                                      else (restrictedCSP, queue)) (csp, []) arcs

fillIn :: CSP -> CSP
fillIn csp = csp { puzzle = Puzzle n assignedGrid }
  where
    Puzzle n _ = puzzle csp
    initGrid = replicate n $ replicate n 0
    assignedGrid =
      Map.foldrWithKey
        (\(r, c) val grid -> update r (update c (const val)) grid)
        initGrid
        (Map.filter (> 0) $ assigns csp)

getDomain :: CSP -> Var -> Domain
getDomain csp var =
  case Map.lookup var $ domains csp of
     Just d -> d
     Nothing -> undefined

selectUnassignedVar :: CSP -> Var
selectUnassignedVar csp =
  head $
  sortBy (\v1 v2 ->
            compare (length (getDomain csp v1)) (length (getDomain csp v2))) $
  filter (\v -> Map.notMember v (assigns csp)) (vars csp)

assignsComplete csp = (Map.size (assigns csp)) == (length (vars csp))

solve :: CSP -> Maybe CSP
solve csp = if assignsComplete csp  then Just csp else
              if anyEmptyDomains csp then Nothing else
                case dropWhile (== Nothing) potentialSolutions of
                  [] -> Nothing
                  (Just csp):_ -> Just csp
  where
    var = selectUnassignedVar csp
    arcs = unassignedArcs csp var
    potentialSolutions = map (\val ->
                                (ac3 (restrictDomainConst csp var val) arcs) >>= solve ) (getDomain csp var)

everyArc csp = concatMap (\var -> allUnassignedArcs csp var) $ vars csp

formatCSPs :: CSP -> Maybe CSP -> String
formatCSPs init solved =
  case solved of
    Just csp -> unlines $ zipWith (\l1 l2 -> (pad l1) ++ " | " ++ (pad l2) ++ "") (lines $ showPuzzle init) (lines $ showPuzzle csp)
    Nothing -> (showPuzzle init) ++ "\n Failed to solve"

  where (Puzzle n _) = puzzle init
        pad str = str ++ (replicate (max 0 (2 * n - (length str))) ' ')

main = do
  tPuzzleStart <- timeInMillis
  
  puzzle <- parsePuzzle
  let csp = buildCSP puzzle
  let nodeCsp = nodeConsistant csp
  let ac3Csp = ac3' nodeCsp (everyArc nodeCsp)
  let solved = ac3Csp >>= solve
  putStr $ seq solved ""
  -- putStrLn $ formatCSPs nodeCsp solved
  -- 
  -- tPuzzleFinish <- timeInMillis
  -- putStrLn ("Time solve: " ++ (show (tPuzzleFinish - tPuzzleStart)) ++ " millis")
