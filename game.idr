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
-- Display functions
--------------------------------------------------------------------------------

showValue : Show a => Maybe a -> String
showValue Nothing  = "."
showValue (Just x) = show x

showRow : Show a => Vect n (Maybe a) -> String
showRow []      = ""
showRow (x::xs) = (showValue x) ++ (showRow xs)

showBoard : Show a => Vect m (Vect n (Maybe a)) -> String
showBoard []      = ""
showBoard (x::xs) = (showRow x) ++ (showBoard xs)

--------------------------------------------------------------------------------
-- JavaScript Engine
--------------------------------------------------------------------------------

JSEvent : Type
JSEvent = Int

continue : (JSEvent -> IO b) -> IO ()
continue {b} cb = mkForeign (FFun "idris_interface.add_callback(%0)" [FFunction FInt (FAny (IO b))] FUnit) cb

display : String -> IO ()
display str = mkForeign (FFun "idris_interface.show(%0)" [FString] FUnit) str

runLoop : a -> (a -> Int -> a) -> (a -> String) -> IO ()
runLoop init trans view = do
  display (view init)
  continue (\x => runLoop (trans init x) trans view)

--------------------------------------------------------------------------------
-- High level game logic
--------------------------------------------------------------------------------

Board : Type
Board = Vect 4 (Vect 4 (Maybe Int))

data Direction = Left | Right | Up | Down

-- For some reason, map isn't working with Vect, so I define my own
vmap : (a -> b) -> Vect n a -> Vect n b
vmap _ [] = []
vmap f (x::xs) = (f x)::(vmap f xs)

move : (Eq a, Num a) => Direction -> Vect m (Vect n (Maybe a)) -> Vect m (Vect n (Maybe a))
move Left  = vmap basicRowOperation
move Right = vmap (reverse . basicRowOperation . reverse)
move Up    = transposeArray . (move Left) . transposeArray
move Down  = transposeArray . (move Right) . transposeArray

||| Not actually random, just selects the first element!
prndSelect : List a -> Maybe a
prndSelect []      = Nothing
prndSelect (x::xs) = Just x

addRandomPiece : Board -> Board
addRandomPiece arr = case (prndSelect indices) of
    Nothing => arr
    Just idx => unFlattenArray (replaceAt idx (Just 1) flattened)
  where
    flattened : Vect 16 (Maybe Int)
    flattened = flattenArray arr
    indices : List (Fin 16)
    indices = findIndicesFin isNothing flattened

data UserAction = Invalid | Move Direction

getAction : Int -> UserAction
getAction 37 = Move Left
getAction 38 = Move Up
getAction 39 = Move Right
getAction 40 = Move Down
getAction _   = Invalid

initialState : Board
initialState = addRandomPiece (replicate _ (replicate _ Nothing))

transitionFunction : Board -> Int -> Board
transitionFunction b = performAction . getAction
  where
    performAction : UserAction -> Board
    performAction Invalid    = b
    performAction (Move dir) = let b' = move dir b in
      if b == b' then
        b'
      else
        (addRandomPiece b')

main : IO ()
main = runLoop initialState transitionFunction showBoard
