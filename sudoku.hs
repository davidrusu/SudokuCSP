import Control.Monad (replicateM, mapM_, forever)
import Data.List (tails, find, delete, sortBy)
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

data CSP = CSP { vars :: [Var]
               , constraints :: [Rule]
               , assigns :: Map.Map Var Int
               , domains :: Map.Map Var Domain
               , puzzle :: Puzzle
               } deriving (Eq)

instance Show Rule where
  show (Neq a b) = (show a) ++ "/=" ++ (show b)
  show (Const a b) = (show a) ++ ":=" ++ (show b)

rowConstraint :: Int -> Int -> [Rule]
rowConstraint n r = concatMap genConstraints $ tails indices
  where indices = [0..n-1]
        genConstraints [] = []
        genConstraints (c:cs) = map (\c2 -> (Neq (r, c) (r, c2))) cs

squareConstraint n rOffset cOffset = map (\(Neq (r, c) (r2, c2)) -> Neq (r + rOffset, c + cOffset) (r2 + rOffset, c2 + cOffset)) constraints
  where nD3 = n `div` 3
        coords = concatMap (\r-> map (\c-> (r, c)) [0..(nD3-1)]) [0..(nD3-1)]
        constraints :: [Rule]
        constraints = concatMap (\v1 -> map (\v2 -> Neq v1 v2) (filter (/= v1) coords)) coords

genConstraints :: Puzzle -> [Rule]
genConstraints (Puzzle n grid) = rowConstraints ++ colConstraints ++ squareConstraints ++ constConstraints
  where rowConstraints = concatMap (rowConstraint n) [0..n-1]
        colConstraints = map (\(Neq (r, c) (r2, c2)) -> Neq (c, r) (c2, r2)) rowConstraints
        squareConstraints = (squareConstraint n 0 0) ++ (squareConstraint n 0 nD3) ++ (squareConstraint n 0 (2 * nD3))
                            ++ (squareConstraint n nD3 0) ++ (squareConstraint n nD3 nD3) ++ (squareConstraint n nD3 (2 * nD3))
                            ++ (squareConstraint n (2 * nD3) 0) ++ (squareConstraint n (2 * nD3) nD3) ++ (squareConstraint n (2 * nD3) (2 * nD3))
        constConstraints =
          map (\(r, c, v) -> Const (r, c) v) (
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

showPuzzle :: Puzzle -> String
showPuzzle (Puzzle n grid) = 
  let header = (show n) ++ " x " ++ (show n) in 
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
  csp { domains = Map.update (const $ Just [val]) var (domains csp) }


restrictDomainNeq :: CSP -> Var -> Var -> CSP
restrictDomainNeq csp var1 var2 =
  case Map.lookup var1 $ domains csp of
       Just dom1 -> csp {
         domains = Map.update (\dom2 -> Just $ restrict dom1 dom2) var2 (domains csp) }
       Nothing -> undefined
  where neqExists x xs = any (/= x) xs
        restrict :: [Int] -> [Int] -> [Int]
        restrict dom1 dom2 = foldl (\d v-> if neqExists v dom1 then d else delete v d ) dom2 dom2
                                  

nodeConsistant :: CSP -> CSP
nodeConsistant csp = nodeConsistantCSP { constraints = binary }
  where unary = filter (\c -> case c of
                          Const _ _ -> True
                          _         -> False) (constraints csp)
        binary = filter (\c -> case c of
                          Const _ _ -> False
                          _ -> True) (constraints csp)
        nodeConsistantCSP = foldl (\csp (Const var val) -> restrictDomainConst csp var val) csp unary

allArcs :: CSP -> Var -> [(Var, Var)]
allArcs csp v = map (\v2-> (v, v2)) varsToAdd
  where cs = filter (\c -> case c of
                       Neq v1 v2 -> v1 == v || v2 == v
                       _ -> False) $ constraints csp
        varsToAdd = map (\(Neq v1 v2) -> if v1 == v then v2 else v1) cs

anyEmptyDomains csp = (Map.size $ Map.filter (\dom -> length dom == 0) (domains csp)) > 0

ac3 :: CSP -> [(Var, Var)] -> Maybe CSP
ac3 csp [] = Just csp
ac3 csp arcs = if anyEmptyDomains csp
               then Nothing
               else ac3 newCSP newArcs
  where (newCSP, newArcs) = foldl (\(csp, queue) (var1, var2) -> let csp2 = restrictDomainNeq csp var1 var2 in
                                     if (getDomain csp2 var2) /= (getDomain csp var2) then (csp2, queue ++ (allArcs csp2 var2)) else (csp2, queue)) (csp, []) arcs

fillIn :: CSP -> Puzzle
fillIn csp = Puzzle n assignedGrid
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
getDomain csp var = case Map.lookup var $ domains csp of
  Just d -> d
  Nothing -> undefined

getConstraints :: CSP -> Var -> Var -> [Rule]
getConstraints csp v1 v2 = filter (\(Neq v3 v4) -> v1 == v3  && v2 == v4) $ constraints csp

constraintsHold :: Map.Map Var Int -> [Rule] -> Bool
constraintsHold vars [] = True
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

updateAssigns :: CSP -> (Var, Int) -> CSP
updateAssigns csp (var, val) = csp { assigns = newAssigns }
  where
    newAssigns :: Map.Map Var Int
    newAssigns = Map.update (const $ Just val) var $ assigns csp

testAssign :: CSP -> (Var, Int) -> Bool
testAssign csp (var, assign) = constraintsHold updatedAssigns relaventConstraints
  where
    updatedAssigns = assigns $ updateAssigns csp (var, assign)
    newAssigns :: [Var]
    newAssigns = map fst $ Map.toList $ Map.filter (> 0) $ updatedAssigns
    relaventConstraints =
      (concatMap (\v -> getConstraints csp v var) $ newAssigns) ++
      (concatMap (\v -> getConstraints csp var v) $ newAssigns)

selectUnassignedVar csp =
  fst $ head $
  sortBy (\(v1,_) (v2,_) ->
            compare (length (getDomain csp v1)) (length (getDomain csp v2))) $
  Map.toList $ Map.filter (<= 0) (assigns csp)

solve :: CSP -> Maybe CSP
solve csp = if (Map.size $ Map.filter (<= 0) (assigns csp)) == 0 then Just csp else
              if anyEmptyDomains csp then Nothing else
                if consistantValues == [] then Nothing else
                  case dropWhile (== Nothing) potentialSolutions of
                    [] -> Nothing
                    (Just csp):_ -> Just csp
  where
    var = selectUnassignedVar csp
    consistantValues = filter (\val -> testAssign csp (var, val)) (getDomain csp var)
    arcs = allArcs csp var
    potentialSolutions = map (\val ->
                                (ac3 (updateAssigns csp (var, val)) arcs) >>= solve ) consistantValues

everyArc csp = concatMap (\var -> allArcs csp var) $ vars csp

main = do
  tStart <- timeInMillis
  
  puzzle <- parsePuzzle
  let csp = buildCSP puzzle
  let nodeCsp = nodeConsistant csp
  let ac3Csp = ac3 nodeCsp $ everyArc nodeCsp
  
  putStrLn $ showPuzzle puzzle
  case ac3Csp >>= solve of
    Just csp -> putStrLn $ showPuzzle $ fillIn csp
    Nothing -> putStrLn "Failed to solve"
  
  tFinish <- timeInMillis
  putStrLn ("Time solve: " ++ (show (tFinish - tStart)) ++ "millis")
