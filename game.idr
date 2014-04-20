import Effect.Exception
import Effect.StdIO
import Effect.Random
import Effect.System

-- Fills in an array 
fillIn : LTE n m -> a -> Vect n a -> Vect m a
fillIn lteZero c []                 = replicate _ c
fillIn (lteSucc w) c (x :: xs)      = x :: (fillIn w c xs)

-- For arguments the a resulting list is not longer than
-- the original list, we usually want to go from n <= m
-- to n <= m + 1.  That is, we apply the successor funciton
-- but only to the right hand side.  This function proves
-- that n <= m implies n <= m + 1
lteSuccR : LTE n m -> LTE n (S m)
lteSuccR lteZero     = lteZero
lteSuccR (lteSucc w) = lteSucc (lteSuccR w)

-- filters out the Nothings from a vector with element of type Maybe a
-- and returns the dependent pair (m ** (Vect m a, LTE m n)) where
-- m is the new length, Vect m a is the filtered list, and LTE m n
-- is a prove that m <= n, that is, that the new list has length
-- less than or equal to the original list.
filterMaybes : Vect n (Maybe a) -> (m ** (Vect m a, LTE m n))
filterMaybes []              = (Z ** ([], lteZero))
filterMaybes (Just x :: xs)  = let (_ ** (ys, w)) = filterMaybes xs in
  (_ ** ((x :: ys), lteSucc w))
filterMaybes (Nothing :: xs) = let (_ ** (ys, w)) = filterMaybes xs in
  (_ ** (ys, lteSuccR w))

--Performs the collapsing of pairs operation of the 2048 game.
--Has the same format as filterMaybes, returning a vector of length
--m and proof that m <= n.
collapsePairs : (Num a, Eq a) => Vect n a -> (m ** (Vect m a, LTE m n))
collapsePairs (x :: xprime :: xs) = 
    if x == xprime then
    	let (_ ** (ys, w)) = collapsePairs xs in (_ ** ((2 * x) :: ys, lteSuccR (lteSucc w)))
    else
        let (_ ** (ys, w)) = collapsePairs (xprime :: xs) in (_ ** (x :: ys, lteSucc w))
collapsePairs (x :: [])           = (_ ** ([x], lteSucc lteZero))
collapsePairs []                  = (_ ** ([], lteZero))

--- The 2048 Game

-- Transitivity of the <= operator
-- m <= n and n <= k impy m <= k
lteTrans : LTE n m -> LTE m l -> LTE n l
lteTrans lteZero _               = lteZero
lteTrans (lteSucc w) (lteSucc z) = lteSucc (lteTrans w z)

-- The basic row operation of the 2048 game.
-- Combines the operations of filterMaybes and collapsePairs,
-- and combines their proofs, and transivity of <=, to
-- prove that the result of applying both operations is
-- a shorter vector than the original.  This proof is used
-- to apply the fillIn function.
basicRowOperation : (Eq a, Num a) => Vect n (Maybe a) -> Vect n (Maybe a)
basicRowOperation xs = let (m ** (ys, w)) = filterMaybes xs in let
  (l ** (zs, wPrime)) = collapsePairs ys in
  (fillIn (lteTrans wPrime w) Nothing (map Just zs))

-- The basic board operations of the 2048 game

-- Takes the transpose of a rectangular array
transposeArray : Vect m (Vect n a) -> Vect n (Vect m a)
transposeArray []        = replicate _ []
transposeArray (x :: xs) = zipWith (::) x (transposeArray xs)

MaybeArray : Nat -> Nat -> Type -> Type
MaybeArray m n a = Vect m (Vect n (Maybe a))

leftMove : (Eq a, Num a) => MaybeArray m n a -> (MaybeArray m n a)
leftMove = map basicRowOperation

rightMove : (Eq a, Num a) => MaybeArray m n a -> (MaybeArray m n a)
rightMove = map (reverse . basicRowOperation . reverse)

upMove : (Eq a, Num a) => MaybeArray m n a -> (MaybeArray m n a)
upMove = transposeArray . leftMove . transposeArray

downMove : (Eq a, Num a) => MaybeArray m n a -> (MaybeArray m n a)
downMove = transposeArray . rightMove . transposeArray

||| Find the indices of all elements that satisfy some test
total findIndicesFin : (a -> Bool) -> Vect m a -> (p ** Vect p (Fin m))
findIndicesFin p [] = (_ ** [])
findIndicesFin p (x::xs) with (findIndicesFin p xs)
      | (_ ** tail) =
       if p x then
        (_ ** fZ::(map fS tail))
       else
        (_ ** (map fS tail))


---Array flattening
flattenArray : Vect m (Vect n a) -> (Vect (m * n) a)
flattenArray Nil       = Nil
flattenArray (x :: xs) = x ++ (flattenArray xs)

split' : Vect (plus m n) a -> (Vect m a, Vect n a)
split' {m=Z} x                = ([], x)
split' {m=(S k)}{n=l} (x::xs) = let (y, z) = split' {m=k}{n=l} xs in
  (x::y, z)

unFlattenArray : Vect (m * n) a -> (Vect m (Vect n a)) 
unFlattenArray {m=Z} Nil = Nil
unFlattenArray {m=(S k)}{n=l} x = let (y, z) = split' {m=l}{n=k*l}  x in
  (y :: (unFlattenArray z))


-- Display functions
showValue : Show a => Maybe a -> String
showValue Nothing  = "...."
showValue (Just x) = pack (List.take 4 (unpack ((show x) ++ "....")))

showRow : Show a => Vect n (Maybe a) -> String
showRow [] = ""
showRow (x::xs) = (showValue x) ++ " " ++ (showRow xs)

showBoard : Show a => Vect m (Vect n (Maybe a)) -> String
showBoard [] = ""
showBoard (x::xs) = (showRow x) ++ "\n" ++ (showBoard xs)


-- One iteration of the 2048 game
Board : Type
Board = MaybeArray 4 4 Int

movePeices : Char -> Board -> {[EXCEPTION String]} Eff IO (Board)
movePeices 'a' b = return (leftMove b)
movePeices 'd' b = return (rightMove b)
movePeices 'w' b = return (upMove b)
movePeices 's' b = return (downMove b)
movePeices 'x' b = raise "You have quit."
movePeices _ b = return b

-- My version of rndFin.  Unlike the function in Effects.Random,
-- rndFin' k takes all possible values in Fin (S k).  That is,
-- it takes values 0,1,...,k.  Even though this is different
-- to the function rndInt 0 k, which only takes values in
-- 0,1,...,k-1, it seems more natural since we would expect
-- that the rndFin function be uniform on the type Fin (S k).
rndFin' : (k : Nat) -> { [RND] } Eff m (Fin (S k))
rndFin' k = do x <- rndFin (S k)
               return (fixStrengthened (strengthen x))
  where fixStrengthened : Either (Fin (S (S n))) (Fin (S n)) -> Fin (S n)
        fixStrengthened (Left _)  = fZ
        fixStrengthened (Right y) = y

-- Select a random element from an array, or raise an exception
-- if the array is empty
selectRandom : Vect n a -> {[RND, EXCEPTION String]} Eff IO (a)
selectRandom {n=Z}     _ = raise "Game Over"
selectRandom {n=(S k)} x = return (Vect.index !(rndFin' k)  x)

addRandomPeice : Board -> {[RND, EXCEPTION String]} Eff IO (Board)
addRandomPeice arr =
	let flattened = flattenArray arr in
	  let (_ ** maybeIndices) = findIndicesFin isNothing flattened in
	    do
	    	insertionIndex <- selectRandom maybeIndices
	    	return (unFlattenArray (replaceAt insertionIndex (Just 2) flattened))

mainLoop : Board -> {[RND, STDIO, EXCEPTION String]} Eff IO (Board)
mainLoop b = do
	putStrLn $ showBoard b
	c <- getChar
	b1 <- movePeices c b
	if b == b1 then
		mainLoop b1
	else
		do
			b2 <- addRandomPeice b1
			mainLoop b2

startGame : { [RND, STDIO, SYSTEM, EXCEPTION String] } Eff IO ()
startGame = do
	srand $ prim__zextInt_BigInt !time
	initialBoard <- addRandomPeice $ replicate _ (replicate _ Nothing)
	mainLoop initialBoard
	return ()
	

main : IO ()
main = run startGame

  
