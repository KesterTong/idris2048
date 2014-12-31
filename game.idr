import Tilinggameengine

--------------------------------------------------------------------------------
-- Operations on individual rows
--------------------------------------------------------------------------------

||| Fills in an array 
fillIn : LTE n m -> a -> Vect n a -> Vect m a
fillIn LTEZero c []            = replicate _ c
fillIn (LTESucc w) c (x :: xs) = x :: (fillIn w c xs)

||| Takes a proof that n <= m and gives a proof that n <= m + 1
LTESuccR : LTE n m -> LTE n (S m)
LTESuccR LTEZero     = LTEZero
LTESuccR (LTESucc w) = LTESucc (LTESuccR w)

||| Filters out the Nothings from a vector of maybes.
|||
||| Takes a vector of length n with elements of type Maybe a
||| and returns the dependent pair (m ** (Vect m a, LTE m n)) where
||| m is the new length, Vect m a is the filtered list, and LTE m n
||| is a prove that m <= n, that is, that the new list has length
||| less than or equal to the original list.
filterMaybes : Vect n (Maybe a) -> (m ** (Vect m a, LTE m n))
filterMaybes []              = (Z ** ([], LTEZero))
filterMaybes (Just x :: xs)  = let (_ ** (ys, w)) = filterMaybes xs in
  (_ ** ((x :: ys), LTESucc w))
filterMaybes (Nothing :: xs) = let (_ ** (ys, w)) = filterMaybes xs in
  (_ ** (ys, LTESuccR w))

||| The collapsing of pairs operation of the 2048 game.
|||
||| Takes a vector of elements of type a, and performs the "collapsing"
||| operation of the 2048 game.  This takes adjacent pairs, and if they
||| are equal, combines them into a single element with double the value.
||| Returns a vector of length m and proof that m <= n.
collapsePairs : (Num a, Eq a) => Vect n a -> (m ** (Vect m a, LTE m n))
collapsePairs (x::x'::xs) = 
  if x == x' then
    let (_ ** (ys, w)) = collapsePairs xs in (_ ** ((x + 1) :: ys, LTESuccR (LTESucc w)))
  else
     let (_ ** (ys, w)) = collapsePairs (x' :: xs) in (_ ** (x :: ys, LTESucc w))
collapsePairs (x::[])     = (_ ** ([x], LTESucc LTEZero))
collapsePairs []          = (_ ** ([], LTEZero))

||| Proof of transitivity of the <= operator
|||
||| Takes proofs that n <= m and m <= l and gives a proof that n <= l
lteTrans : LTE n m -> LTE m l -> LTE n l
lteTrans {l} LTEZero     _            = LTEZero {right=l}
lteTrans     (LTESucc p) (LTESucc p') = LTESucc (lteTrans p p')

||| The basic row operation of the 2048 game.
|||
||| Combines the operations of filterMaybes and collapsePairs,
||| and combines their proofs, and transitivity of <=, to
||| prove that the result of applying both operations is
||| a shorter vector than the original.  This proof is used
||| to apply the fillIn function.
basicRowOperation : (Eq a, Num a) => Vect n (Maybe a) -> Vect n (Maybe a)
basicRowOperation xs = let (m ** (ys, w)) = filterMaybes xs in let
  (l ** (zs, wPrime)) = collapsePairs ys in
  (fillIn (lteTrans wPrime w) Nothing (map Just zs))

--------------------------------------------------------------------------------
-- Operations on the game board
--------------------------------------------------------------------------------

||| Takes the transpose of a rectangular array
transposeArray : Vect n (Vect m a) -> Vect m (Vect n a)
transposeArray []      = replicate _ []
transposeArray (x::xs) = zipWith (::) x (transposeArray xs)

||| Flattens a rectangular array
flattenArray : Vect n (Vect m a) -> Vect (n * m) a
flattenArray Nil     = Nil
flattenArray (x::xs) = x ++ (flattenArray xs)

||| Splits an array
split' : Vect (plus n m) a -> (Vect n a, Vect m a)
split' {n=Z} xs                = ([], xs)
split' {n=(S k)}{m=l} (x::xs) = let (ys, zs) = split' {n=k}{m=l} xs in
  (x::ys, zs)

||| Unflattens an array
unFlattenArray : Vect (n * m) a -> Vect n (Vect m a)
unFlattenArray {n=Z} Nil         = Nil
unFlattenArray {n=(S k)}{m=l} xs = let (ys, zs) = split' {n=l}{m=k*l} xs in
  (ys :: (unFlattenArray zs))

||| Find the indices of all elements of a vector that satisfy some test
total findIndicesFin : (a -> Bool) -> Vect n a -> List (Fin n)
findIndicesFin f [] = []
findIndicesFin f (x::xs) = let tail = (map FS (findIndicesFin f xs)) in
  if f x then (FZ :: tail) else tail

--------------------------------------------------------------------------------
-- Replicating some functions from std library
--------------------------------------------------------------------------------

-- For some reason, map isn't working with Vect, so I define my own
vmap : (a -> b) -> Vect n a -> Vect n b
vmap _ [] = []
vmap f (x::xs) = (f x)::(vmap f xs)

-- It should be possible to use Effect.Rand.  But for now, the functionaly
-- is replicated here without using monads.

nextRnd : Integer -> Integer
nextRnd x = assert_total $ (1664525 * x + 1013904223) `prim__sremBigInt` (pow 2 32)

||| Generates a random Integer in a given range
rndInt : (rng : Integer) -> Integer -> Integer -> (Integer, Integer)
rndInt rng lower upper = (nextRnd rng, (rng `prim__sremBigInt` (upper - lower)) + lower)

||| Generate a random number in Fin (S `k`)
|||
||| Note that rndFin k takes values 0, 1, ..., k.
rndFin : (rng : Integer) -> (k : Nat) -> (Integer, Fin (S k))
rndFin rng k = assert_total $ let (rng', x) = rndInt rng 0 (toIntegerNat  (S k))
    in (rng', toFin x)
 where toFin : Integer -> Fin (S k)
       toFin x = case integerToFin x (S k) of
                      Just v => v
                      Nothing => toFin (assert_smaller x (x - cast (S k)))

||| Select a random element from a vector
rndSelect' : (rng : Integer) -> Vect (S k) a -> (Integer, a)
rndSelect' {k} rng xs = let (rng', idx) = rndFin rng k in
  (rng', Vect.index idx xs)

||| Select a random element from a list, or Nothing if the list is empty
rndSelect : (rng : Integer) -> List a -> (Integer, Maybe a)
rndSelect rng []      = (rng, Nothing)
rndSelect rng (x::xs) = let (rng', x) = rndSelect' rng (x::(fromList xs)) in
  (rng', Just x)

--------------------------------------------------------------------------------
-- High level game logic
--------------------------------------------------------------------------------

mm : Nat
mm = 4

nn : Nat
nn = 4

Board : Type
Board = Vect mm (Vect nn (Maybe Int))

data GameState = BoardState Board Integer | GameOver

gridSize : GridSize
gridSize = mkGridSize mm nn;

gridForState : GameState -> (CellGrid gridSize)
gridForState (BoardState b _) = map (map (maybe 15 (\x => x))) b
gridForState GameOver         = replicate _ (replicate _ 14)

data Direction = Left | Right | Up | Down

move : Direction -> Board -> Board
move Left  = vmap basicRowOperation
move Right = vmap (reverse . basicRowOperation . reverse)
move Up    = transposeArray . (move Left) . transposeArray
move Down  = transposeArray . (move Right) . transposeArray

addRandomPiece : Board -> Integer -> GameState
addRandomPiece b rng = let (rng', maybeIdx) = rndSelect rng indices in case maybeIdx of
    Nothing => BoardState b rng'
    Just idx => BoardState (unFlattenArray (replaceAt idx (Just 0) flattened))  rng'
  where
    flattened : Vect (mm * nn) (Maybe Int)
    flattened = flattenArray b
    indices : List (Fin (mm * nn))
    indices = findIndicesFin isNothing flattened

data UserAction = Invalid | Move Direction

getAction : Int -> UserAction
getAction 37 = Move Left
getAction 38 = Move Up
getAction 39 = Move Right
getAction 40 = Move Down
getAction _   = Invalid

initialState : GameState
initialState = addRandomPiece (replicate _ (replicate _ Nothing)) 0

isLosingPosition : Board -> Bool
isLosingPosition b = all (\dir => move dir b == b) $ (the (Vect _ Direction)) [Left, Up, Right, Down]

transitionFunction : GameState -> Int -> GameState
transitionFunction GameOver _ = GameOver
transitionFunction (BoardState b rng) charcode = if isLosingPosition b then
    GameOver
  else
    performAction (getAction charcode)
  where
    performAction : UserAction -> GameState
    performAction Invalid    = BoardState b rng
    performAction (Move dir) = let b' = move dir b in
      if b == b' then
        BoardState b' rng
      else
        addRandomPiece b' rng

main : IO ()
main = startEventLoop gridSize initialState transitionFunction gridForState
