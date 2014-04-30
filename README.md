#2048 in Idris
This project ports the game [2048](http://gabrielecirulli.github.io/2048/) to the dependently typed programming language [Idris](http://www.idris-lang.org/).  Dependently typed languages are interesting because they allow the type system to express much stronger constraints than other languages.  Idris appealed to me because of its emphasis on general purpose programming (as opposed to automated theorem proving) and its Haskell based syntax.  I made this project to learn Idris - 2048 is a good level of complexity for learning the basics of language - and I hope it can help other people who are learning Idris.

This project will be much easier to understand if you are familiar with Haskell.
##Compiling and Running
After installing Idris and cloning this repo, you can type in the console (instructions for OSX)
```bash
idris game.idr -o game -p effects
```
This compiles the file game.idr, to the executable file game.  The flag -p effects instructs the compiler
to user the Effect library, which is needed for IO, exceptions, and random number generation.

To play the game, type
```bash
./game
```

The keys are a, s, d, and w for moving, and x for quit.  Currently, there is no code
to detect winning or losing the game, and the UI is somewhat quirky, but it is good
enough to see that the basic logic of the game is working.

##Discussion
This section discusses the code, with emphasis on the effects of the dependent type system.

###The Main Row-wise Operation
The main operation in 2048 is pushing tiles in a direction.  If we consider a single row of tiles, the move takes a row, e.g.
<table>
    <tr>
        <td>4</td><td>&nbsp;&nbsp;</td><td>2</td><td>2</td>
    </tr>
</table>
moves non-empty tiles to the left
<table>
    <tr>
        <td>4</td><td>2</td><td>2</td><td>&nbsp;&nbsp;</td>
    </tr>
</table>
and then collapses adjacent tiles that have the same number, combining those numbers into a number with double the value. In this case, the two 2's combine into a 4, to give
<table>
    <tr>
        <td>4</td><td>4</td><td>&nbsp;&nbsp;</td><td>&nbsp;&nbsp;</td>
    </tr>
</table>
Note that there is only one pass: the 4's don't immediately combine into an 8.

It would be very easy represent both these processes as functions on lists in Haskell.  We can represent tiles that can either be blank, or have a number, using the Maybe monad.  The first step takes a list of Maybe a's where a is a numeric type, and returns a list of a's where all the Nothing's have been removed.  The function can be written
```haskell
filterMaybes :: [Maybe a] -> [a]
filterMaybes []             = []
filterMaybes (Just x : xs)  = x : filterMaybes xs
filterMaybes (Nothing : xs) = filterMaybes xs
```
The second operation can also be defined recursively.  Tiles are combined, starting from the left.  If two tiles are found that match, they are combined, and we move on to the next tile.  If not, we take the next pair of tiles (that is, the pair which has one tile in common with the pair just tested).  This results in the function
```haskell
collapsePairs :: (Num a, Eq a) => [a] -> [a]
collapsePairs []                = []
collapsePairs (x : [])          = [x]
collapsePairs (x : xprime : xs) = if x == xprime then
    (2 * x) : (collapsePairs xs)
  else
    x : (collapsePairs (xprime : xs))
```

If we started with the list [Just 4, Nothing, Just 2, Just 2], and apply the above functions in order, we get the list [4, 4].  In order to finish the process, we should apply Just to each element, and fill in the remaining two spaces.

But in Haskell, we would have to fill in 4 minus the length of the resulting list.  Since we can't restrict inputs to lists of length 4 or less, we would have to define a more general function that takes a list, fills in the gaps if the length is less than 4, and otherwise truncates it:
```haskell
fillInList :: a -> [a] -> [a]
fillInList c l = if length l < 4 then
    l ++ (replicate (4 - (length l)) c)
  else
  	take 4 l
```
###Implementing the filIn Function in Idris
Idris has types, like Vect n a, which represents a vector of length n and with elements of type a.  It also has types that represent assertions, or propositions.  The type LTE m n represents the proposition that m is less than n.  It is non-empty exactly when m <= n.  An element of LTE m n can be thought of as a witness, or proof, that m <= n.  The fill in function in Idris is given by
```
fillIn : LTE n m -> a -> Vect n a -> Vect m a
fillIn lteZero c []            = replicate _ c
fillIn (lteSucc w) c (x :: xs) = x :: (fillIn w c xs)
```
From the signature, it takes a witness that m <= n, an element of type a, and a vector of length m (of elements of type a) and returns a vector of length n (of elements of type a).  Since the type LTE m n is empty unless m <= n, it is impossible to call fillIn unless m <= n.  This is very useful to know, because on the one hand, we don't have to right logic for cases which we know will never occur (like in the fillInList function), and on the other hand, the type checker will ensure that this function will only be called when m <= n.  We'll show later how this is possible even in the case where the length of the vector varies at run time, like in the game 2048.

As the above shows, dealing with witnesses/proofs is not much more difficult than dealing with recursive data types.  LTE is a generalized algebraic data type, defined in Prelude.Nat by
```
||| Proofs that `n` is less than or equal to `m`
||| @ n the smaller number
||| @ m the larger number
data LTE  : (n, m : Nat) -> Type where
  ||| Zero is the smallest Nat
  lteZero : LTE Z    right
  ||| If n <= m, then n + 1 <= m + 1
  lteSucc : LTE left right -> LTE (S left) (S right)
```
The first constructor, lteZero, represents the fact that 0 <= m for all m, while the second takes a proof that n <= m and gives a proof n + 1 <= m + 1.  So we can define fillIn by recursion on the witness and the vector.  Naively, there would be four cases, two for the witness, by two for the vector.  But because we know that both these type depend on m, there are actually only two cases we need to consider.  When n = Z (the Nat type uses Z instead of zero to distinguish it from the Integer type), then there is only one case that applies for constructing the witness, lteZero, and for the vector, the empty vector. When n=Sk for some k, then the witness must have the form lteSucc w and the vector must have the form y :: ys.  These two cases are given above.

Verbally, the logic of the above functions is as follows: given n <= m and a vector of length n, we want to fill in the vector m, with the provided constant, to become a vector of length n.  There are two cases.  In the case n = Z, then we can construct the vector by replicating the constant m times.  In the case of n = k + 1, we by induction on the definition of n <= m, there must be and l such that m = l + 1 and k <= l.  Furthermore, the vector has length k + 1 and so must have the form x :: xs, where xs has length k.  Then we can apply the function fillIn to the vector xs, to get a vector of length l, since we know that k <= l.  Call this vector (fillIn w c xs).  The vector x :: (fillIn w c xs) has length l + 1, which equals m.  This is x :: xs filled in to length m.

The compiler is able to automatically make these inferences, so that if we load this code into the interpreter (first run idris -p effects to load the interpreter with the effects package), we can query the function fillIn, and the interpreter will confirm that it is total, i.e. guaranteed to return a value:
```
$ idris -p effects
     ____    __     _                                          
    /  _/___/ /____(_)____                                     
    / // __  / ___/ / ___/     Version 0.9.12
  _/ // /_/ / /  / (__  )      http://www.idris-lang.org/      
 /___/\__,_/_/  /_/____/       Type :? for help                

Idris> :l game
*game> :total fillIn 
Main.fillIn is Total
```

It's worth noting some other things.  Some variables can be left out entirely, like the first argument to replicate.  This is because the compiler can infer that this must be n.  n is not actually an argument to the function, but it is an implicit argument, which we will see more of later.

###Implementing the Other Functions
Now that we have the fillIn function, we can work backwards and construct the filterMaybes and collapsePairs functions.  The filterMaybes function looks like this:
```
filterMaybes : Vect n (Maybe a) -> (m ** (Vect m a, LTE m n))
filterMaybes []              = (Z ** ([], lteZero))
filterMaybes (Just x :: xs)  = let (_ ** (ys, w)) = filterMaybes xs in
  (_ ** ((x :: ys), lteSucc w))
filterMaybes (Nothing :: xs) = let (_ ** (ys, w)) = filterMaybes xs in
  (_ ** (ys, lteSuccR w))
```
The return value of filterMaybes is a dependent pair.  A dependent pair is a pair when the type of the second value can depend of the first value.  In this case, the first value is a Nat (this is implicit) named m, and the second value is a regular pair of a vector of length m, and a proof that m <= n.  The reason for using a dependent pair, is that if we wrote the signature Vect n (Maybe a) -> (Vect m a, LTE m n), then m would be an implicit argument.  This doesn't suit our needs as the value of m should be determined within the function, not by the caller.

The function needs to compute two things: the new vector, and the proof that the vector has length less than n.  For example, in the case where the vector has the form (Just x :: xs), we can apply filterMaybes to xs.  Let the resulting vector be ys, which has length less or equal to the length of xs, which is n - 1.  Let w be the witness to this.  Therefore lteSucc w is a witness to the length of (x :: ys) being less than or equal to n.  In the other case, (Nothing ::xs), we want to use the vector ys in the return value.  While ys has length less than n - 1, so it also has length less than n, applying lteSucc doesn't give the appropriate witness: it proves that the length of ys plus one, is less than or equal to n - 1.  So we have to construct our own function to give a witness of the right type, which is named lteSuccR, and defined in game.idr.

The construction of collapsePairs is exactly the same, with the code given by
```
collapsePairs : (Num a, Eq a) => Vect n a -> (m ** (Vect m a, LTE m n))
collapsePairs (x :: xprime :: xs) = 
    if x == xprime then
    	let (_ ** (ys, w)) = collapsePairs xs in (_ ** ((2 * x) :: ys, lteSuccR (lteSucc w)))
    else
        let (_ ** (ys, w)) = collapsePairs (xprime :: xs) in (_ ** (x :: ys, lteSucc w))
collapsePairs (x :: [])           = (_ ** ([x], lteSucc lteZero))
collapsePairs []                  = (_ ** ([], lteZero))

```

In order to put these together, want to apply filterMaybes, to get a vector ys, then apply collapsePairs to this vector to get a vector zs.  In addition, this gives two proofs, that the length of ys is less than n, and the length of zs is less than the length of ys.  In order apply the function fillIn, we need to construct a proof that the length of zs is less than n.  This applies by transitivity of <=, which we prove.  This "proof" is a function that takes a witness that n <= m and m <= l, and gives a witness that n <= l.  It is also defined in game.idr with the name lteTrans.  The complete row operation is given by

```
basicRowOperation : (Eq a, Num a) => Vect n (Maybe a) -> Vect n (Maybe a)
basicRowOperation xs = let (m ** (ys, w)) = filterMaybes xs in let
  (l ** (zs, wPrime)) = collapsePairs ys in
  (fillIn (lteTrans wPrime w) Nothing (map Just zs))
```

As before, the compiler/interpreter knows that the function basicRowOperation is total.  This is a cool property, because the function is proven to be total even though we didn't define the extra cases like in fillInList.

...to be continued...
