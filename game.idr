import Effect.Exception
import Effect.StdIO
import Effect.Random
import Effect.System

-- Fills in an array 
fillIn : LTE m n -> Vect m a -> a -> Vect n a
fillIn lteZero [] c                 = replicate _ c
fillIn (lteSucc w) (x :: xs) c      = x :: (fillIn w xs c)

-- For arguments the a resulting list is not longer than
-- the original list, we usually want to go from m <= n
-- to m <= n + 1.  That is, we apply the successor funciton
-- but only to the right hand side.
lteSuccR : LTE m n -> LTE m (S n)
lteSuccR lteZero     = lteZero
lteSuccR (lteSucc w) = lteSucc (lteSuccR w)

filterMaybes : Vect n (Maybe a) -> (m ** (Vect m a, LTE m n))
filterMaybes []              = (Z ** ([], lteZero))
filterMaybes (Just x :: xs)  = let (_ ** (ys, w)) = filterMaybes xs in
  (_ ** ((x :: ys), lteSucc w))
filterMaybes (Nothing :: xs) = let (_ ** (ys, w)) = filterMaybes xs in
  (_ ** (ys, lteSuccR w))

collapsePairs : (Num a, Eq a) => Vect n a -> (m ** (Vect m a, LTE m n))
collapsePairs (x :: xprime :: xs) = 
    if x == xprime then
    	let (_ ** (ys, w)) = collapsePairs xs in (_ ** ((2 * x) :: ys, lteSuccR (lteSucc w)))
    else
        let (_ ** (ys, w)) = collapsePairs (xprime :: xs) in (_ ** (x :: ys, lteSucc w))
collapsePairs (x :: [])           = (_ ** ([x], lteSucc lteZero))
collapsePairs []                  = (_ ** ([], lteZero))

--- The 2048 Game

-- Transitivity of the less-than-or-equal-to operator
-- m <= n and n <= k impy m <= k
lteTrans : LTE m n -> LTE n k -> LTE m k
lteTrans lteZero _               = lteZero
lteTrans (lteSucc w) (lteSucc z) = lteSucc (lteTrans w z)

-- The basic row operation of the 2048 game: 
basicRowOperation : (Eq a, Num a) => Vect n (Maybe a) -> Vect n (Maybe a)
basicRowOperation xs = let (m ** (ys, w)) = filterMaybes xs in let
  (l ** (zs, wPrime)) = collapsePairs ys in
  (fillIn (lteTrans wPrime w) (map Just zs) Nothing)

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

--movePeices : Char -> Board -> {[RND, EXCEPTION String]} Eff IO (Board)
--movePeices '' = do
--	return $ b

movePeices : Char -> Board -> {[EXCEPTION String]} Eff IO (Board)
movePeices 'a' b = return (leftMove b)
movePeices 'd' b = return (rightMove b)
movePeices 'w' b = return (upMove b)
movePeices 's' b = return (downMove b)
movePeices 'x' b = raise "You have quit."
movePeices _ b = return b

-- Fixes a bug in Effects.Random.rndFin, where it throws
-- an execption  when rndFin Z is called, instead
-- of always returning fZ
rndFin' : (k : Nat) -> { [RND] } Eff m (Fin (S k))
rndFin' Z     = return fZ
rndFin' (S k) = rndFin (S k)

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

  
