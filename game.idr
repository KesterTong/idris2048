import Effect.Exception
import Effect.StdIO
import Effect.Random
import Effect.System

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
collapsePairs (x :: xprime :: xs) = 
  if x == xprime then
    let (_ ** (ys, w)) = collapsePairs xs in (_ ** ((2 * x) :: ys, lteSuccR (lteSucc w)))
  else
     let (_ ** (ys, w)) = collapsePairs (xprime :: xs) in (_ ** (x :: ys, lteSucc w))
collapsePairs (x :: [])           = (_ ** ([x], lteSucc lteZero))
collapsePairs []                  = (_ ** ([], lteZero))

||| Proof of transitivity of the <= operator
|||
||| Takes proofs that n <= m and m <= l and gives a proof that n <= l
lteTrans : LTE n m -> LTE m l -> LTE n l
lteTrans lteZero _               = lteZero
lteTrans (lteSucc w) (lteSucc z) = lteSucc (lteTrans w z)

||| The basic row operation of the 2048 game.
|||
||| Combines the operations of filterMaybes and collapsePairs,
||| and combines their proofs, and transivity of <=, to
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
transposeArray : Vect m (Vect n a) -> Vect n (Vect m a)
transposeArray []        = replicate _ []
transposeArray (x :: xs) = zipWith (::) x (transposeArray xs)

||| Flattens a rectangular array
flattenArray : Vect m (Vect n a) -> (Vect (m * n) a)
flattenArray Nil       = Nil
flattenArray (x :: xs) = x ++ (flattenArray xs)

||| Splits an array
split' : Vect (plus m n) a -> (Vect m a, Vect n a)
split' {m=Z} x                = ([], x)
split' {m=(S k)}{n=l} (x::xs) = let (y, z) = split' {m=k}{n=l} xs in
  (x::y, z)

||| Unflattens an array
unFlattenArray : Vect (m * n) a -> (Vect m (Vect n a)) 
unFlattenArray {m=Z} Nil = Nil
unFlattenArray {m=(S k)}{n=l} x = let (y, z) = split' {m=l}{n=k*l}  x in
  (y :: (unFlattenArray z))

||| Find the indices of all elements of a vector that satisfy some test
total findIndicesFin : (a -> Bool) -> Vect m a -> (p ** Vect p (Fin m))
findIndicesFin p [] = (_ ** [])
findIndicesFin p (x::xs) with (findIndicesFin p xs)
      | (_ ** tail) =
       if p x then
        (_ ** fZ::(map fS tail))
       else
        (_ ** (map fS tail))

||| Randomly selects an element in a finite set of given size
||| 
||| Unlike the function Effects.Random.Fin, rndFin' k takes all possible
||| values in Fin (S k).  That is, it takes values 0,1,...,k.
rndFin' : (k : Nat) -> { [RND] } Eff m (Fin (S k))
rndFin' k = do x <- rndFin (S k)
               return (fixStrengthened (strengthen x))
  where fixStrengthened : Either (Fin (S (S n))) (Fin (S n)) -> Fin (S n)
        fixStrengthened (Left _)  = fZ
        fixStrengthened (Right y) = y

||| Select a random element from a vector.
||| 
||| Selects a random element from a vector, or raises an exception
||| if the array is empty.
selectRandom : Vect n a -> {[RND, EXCEPTION String]} Eff IO (a)
selectRandom {n=Z}     _ = raise "Game Over"
selectRandom {n=(S k)} x = return (Vect.index !(rndFin' k)  x)

--------------------------------------------------------------------------------
-- Display functions
--------------------------------------------------------------------------------

showValue : Show a => Maybe a -> String
showValue Nothing  = "...."
showValue (Just x) = pack (List.take 4 (unpack ((show x) ++ "....")))

showRow : Show a => Vect n (Maybe a) -> String
showRow [] = ""
showRow (x::xs) = (showValue x) ++ " " ++ (showRow xs)

showBoard : Show a => Vect m (Vect n (Maybe a)) -> String
showBoard [] = ""
showBoard (x::xs) = (showRow x) ++ "\n" ++ (showBoard xs)

--------------------------------------------------------------------------------
-- High level game logic
--------------------------------------------------------------------------------

Board : Type
Board = Vect 4 (Vect 4 (Maybe Int))

data Direction = Left | Right | Up | Down

move : (Eq a, Num a) => Direction -> Vect m (Vect n (Maybe a)) -> Vect m (Vect n (Maybe a))
move Left  = map basicRowOperation
move Right = map (reverse . basicRowOperation . reverse)
move Up    = transposeArray . (move Left) . transposeArray
move Down  = transposeArray . (move Right) . transposeArray

addRandomPiece : Board -> {[RND, EXCEPTION String]} Eff IO (Board)
addRandomPiece arr =
  let flattened = flattenArray arr in
    let (_ ** maybeIndices) = findIndicesFin isNothing flattened in
      do
        insertionIndex <- selectRandom maybeIndices
        return (unFlattenArray (replaceAt insertionIndex (Just 2) flattened))

data UserAction = Quit | Invalid | Move Direction

getAction : Char -> UserAction
getAction 'a' = Move Left
getAction 'd' = Move Right
getAction 'w' = Move Up
getAction 's' = Move Down
getAction 'x' = Quit
getAction _   = Invalid

mainLoop : Board -> {[RND, STDIO, EXCEPTION String]} Eff IO (Board)
mainLoop b = do putStrLn (showBoard b)
                c <- getChar
                performAction (getAction c)
    where performAction : UserAction -> {[RND, STDIO, EXCEPTION String]} Eff IO (Board)
          performAction Quit       = raise "You have quit"
          performAction Invalid    = mainLoop b
          performAction (Move dir) = let b' = move dir b in
            if b == b' then
              mainLoop b'
            else
              do
                b'' <- addRandomPiece b'
                mainLoop b''

startGame : { [RND, STDIO, SYSTEM, EXCEPTION String] } Eff IO ()
startGame = do
  srand $ prim__zextInt_BigInt !time
  initialBoard <- addRandomPiece (replicate _ (replicate _ Nothing))
  mainLoop initialBoard
  return ()	

main : IO ()
main = run startGame
