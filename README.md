#2048 in Idris
This project ports the game [2048](http://gabrielecirulli.github.io/2048/) to the dependently typed programming language [Idris](www.idris-lang.org/).  Depenently typed languages are interesting because they allow the type system to express much stronger constraints than other lanaguges.  Idris appealed to me because of its emphasis on general purpose programming (as opposed to automated theorem proving) and its Haskell based syntax.  I made this project to learn Idris - 2048 is a good level of complexity for learning the basics of language - and I hope it can help other people who are learning Idris.

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

Idris has types, like Vect n a, which represents a vector of length n and with elements of type a.  It also has types that represent assertions, or propositions.  The type LTE m n represnts the proposition that m is less than n.  It is non-empty exactly when m <= n.  An element of LTE m n can be thought of as a witness, or proof, that m <= n.  The fill in function in Idris is given by
```
fillIn : LTE m n -> a -> Vect m a -> Vect n a
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
The first constructor, lteZero, represents the fact that 0 <= m for all m, while the second takes a proof that n <= m and gives a proof n + 1 <= m + 1.  So we can define fillIn by recursion on the witness and the vector.  But because we (and the compiler) know something about the type of the witness an the type of the vector, there are two cases, not four.  When m=Z, then there is only one case that applies for constructing the witness, lteZero, and for the vector, the empty vector. When m=Sk for some k, then the witness must have the form lteSucc w and the vector must have the form y :: ys.

The compiler is able to automatically make these inferences, so that if we load this code into the interpreter (first run idris -p effects to load the interpreter with the effects package) and run the commands
```
:l game
:total fillIn
```
the interpreter will report that fillIn is a total function, i.e. we haven't left any cases out.


It's worth noting some other things.  Some variables can be left out entirely, like the first argument to repllicate.  This is because the compiler can infer that this must be n.  n is not actually an argument to the function, but it is an implicit argument, which we will see more of later.
