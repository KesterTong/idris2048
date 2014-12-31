--------------------------------------------------------------------------------
-- Operations on individual rows
--------------------------------------------------------------------------------

||| Fills in an array 
fillIn : LTE n m -> a -> Vect n a -> Vect m a
fillIn lteZero c []            = replicate _ c
fillIn (lteSucc w) c (x :: xs) = x :: (fillIn w c xs)

||| Takes a proof that n <= m and gives a proof that n <= m + 1
lteSuccR : LTE n m -> LTE n (S m)
lteSuccR lteZero     = lteZero
lteSuccR (lteSucc w) = lteSucc (lteSuccR w)

||| Filters out the Nothings from a vector of maybes.
|||
||| Takes a vector of length n with elements of type Maybe a
||| and returns the dependent pair (m ** (Vect m a, LTE m n)) where
||| m is the new length, Vect m a is the filtered list, and LTE m n
||| is a prove that m <= n, that is, that the new list has length
||| less than or equal to the original list.
filterMaybes : Vect n (Maybe a) -> (m ** (Vect m a, LTE m n))
filterMaybes []              = (Z ** ([], lteZero))
filterMaybes (Just x :: xs)  = let (_ ** (ys, w)) = filterMaybes xs in
  (_ ** ((x :: ys), lteSucc w))
filterMaybes (Nothing :: xs) = let (_ ** (ys, w)) = filterMaybes xs in
  (_ ** (ys, lteSuccR w))

||| The collapsing of pairs operation of the 2048 game.
|||
||| Takes a vector of elements of type a, and performs the "collapsing"
||| operation of the 2048 game.  This takes adjacent pairs, and if they
||| are equal, combines them into a single element with double the value.
||| Returns a vector of length m and proof that m <= n.
collapsePairs : (Num a, Eq a) => Vect n a -> (m ** (Vect m a, LTE m n))
collapsePairs (x::x'::xs) = 
  if x == x' then
    let (_ ** (ys, w)) = collapsePairs xs in (_ ** ((x + 1) :: ys, lteSuccR (lteSucc w)))
  else
     let (_ ** (ys, w)) = collapsePairs (x' :: xs) in (_ ** (x :: ys, lteSucc w))
collapsePairs (x::[])     = (_ ** ([x], lteSucc lteZero))
collapsePairs []          = (_ ** ([], lteZero))

||| Proof of transitivity of the <= operator
|||
||| Takes proofs that n <= m and m <= l and gives a proof that n <= l
lteTrans : LTE n m -> LTE m l -> LTE n l
lteTrans lteZero _                = lteZero
lteTrans (lteSucc p) (lteSucc p') = lteSucc (lteTrans p p')

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
findIndicesFin f (x::xs) = let tail = (map fS (findIndicesFin f xs)) in
  if f x then (fZ :: tail) else tail

--------------------------------------------------------------------------------
-- Replicating some functions from std library
--------------------------------------------------------------------------------

-- For some reason, map isn't working with Vect, so I define my own
vmap : (a -> b) -> Vect n a -> Vect n b
vmap _ [] = []
vmap f (x::xs) = (f x)::(vmap f xs)


toIntNat : Nat -> Int
toIntNat n = toIntNat' n 0 where
  toIntNat' : Nat -> Int -> Int
  toIntNat' Z     x = x
  toIntNat' (S n) x = toIntNat' n (x + 1)

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
-- JavaScript Engine
--------------------------------------------------------------------------------

data GridSize = mkGridSize Nat Nat

CellGrid : GridSize -> Type
CellGrid (mkGridSize m n) = Vect m (Vect n Int)

EncodeGrid : (size : GridSize) -> CellGrid size -> String
EncodeGrid (mkGridSize Z _) _ = ""
EncodeGrid (mkGridSize (S k) _) (r::rs) = (pack (vmap chr r)) ++ (EncodeGrid (mkGridSize k _) rs)

JSEvent : Type
JSEvent = Int

getNextEvent : (JSEvent -> IO ()) -> IO ()
getNextEvent cb = mkForeign (FFun "idris_interface.get_next_event(%0)" [FFunction FInt (FAny (IO ()))] FUnit) cb

initDisplay : Int -> Int -> IO ()
initDisplay m n = mkForeign (FFun "idris_interface.init_display(%0, %1)" [FInt, FInt] FUnit) m n

display : String -> IO ()
display str = mkForeign (FFun "idris_interface.show(%0)" [FString] FUnit) str

runEventLoop : (size : GridSize) -> a -> (a -> Int -> a) -> (a -> (CellGrid size)) -> IO ()
runEventLoop (mkGridSize m n) init trans view = do
  display (EncodeGrid (mkGridSize m n) (view init))
  getNextEvent (\x => runEventLoop (mkGridSize m n) (trans init x) trans view)

startEventLoop : (size : GridSize) -> a -> (a -> Int -> a) -> (a -> (CellGrid size)) -> IO ()
startEventLoop (mkGridSize m n) init trans view = do
  initDisplay (toIntNat m) (toIntNat n)
  runEventLoop (mkGridSize m n) init trans view

--------------------------------------------------------------------------------
-- High level game logic
--------------------------------------------------------------------------------

mm : Nat
mm = 4

nn : Nat
nn = 4

Board : Type
Board = Vect mm (Vect nn (Maybe Int))

gridSize : GridSize
gridSize = mkGridSize mm nn;

gridForState : (Board, Integer) -> (CellGrid gridSize)
gridForState (b, i) = map (map (maybe 15 (\x => x))) b

data Direction = Left | Right | Up | Down

move : (Eq a, Num a) => Direction -> Vect m (Vect n (Maybe a)) -> Vect m (Vect n (Maybe a))
move Left  = vmap basicRowOperation
move Right = vmap (reverse . basicRowOperation . reverse)
move Up    = transposeArray . (move Left) . transposeArray
move Down  = transposeArray . (move Right) . transposeArray

||| Not actually random, just selects the first element!
prndSelect : List a -> Maybe a
prndSelect []      = Nothing
prndSelect (x::xs) = Just x

addRandomPiece : (Board, Integer) -> (Board, Integer)
addRandomPiece (arr, i) = let (i', x) = rndSelect i indices in case x of
    Nothing => (arr, i')
    Just idx => (unFlattenArray (replaceAt idx (Just 0) flattened), i')
  where
    flattened : Vect (mm * nn) (Maybe Int)
    flattened = flattenArray arr
    indices : List (Fin (mm * nn))
    indices = findIndicesFin isNothing flattened

data UserAction = Invalid | Move Direction

getAction : Int -> UserAction
getAction 37 = Move Left
getAction 38 = Move Up
getAction 39 = Move Right
getAction 40 = Move Down
getAction _   = Invalid

initialState : (Board, Integer)
initialState = addRandomPiece (replicate _ (replicate _ Nothing), 0)

transitionFunction : (Board, Integer) -> Int -> (Board, Integer)
transitionFunction (b, i) = performAction . getAction
  where
    performAction : UserAction -> (Board, Integer)
    performAction Invalid    = (b, i)
    performAction (Move dir) = let b' = move dir b in
      if b == b' then
        (b', i)
      else
        addRandomPiece (b', i)

main : IO ()
main = startEventLoop gridSize initialState transitionFunction gridForState
