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
``
