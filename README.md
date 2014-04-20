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
to detect winning or losing the game, and the UI is someone quirky, but it is good
enough to see that the basic logic of the game is working.

##Discussion
This section discusses the code, with emphasis on the effects of the dependent type system.

###The Main Row-wise Operation
The main operation in 2048 is pushing cells in a direction.  If we consider a single row of cells, move takes a row, e.g.
<table>
    <tr>
        <td>4</td><td>_</td><td>2</td><td>2</td>
    </tr>
</table>
moves non-empty cells to the left
<table>
    <tr>
        <td>4</td><td>2</td><td>2</td><td>_</td>
    </tr>
</table>
and then collapses adjacent cells that have the same number, combining those numbers into a number with double the value. In this case, the two 2's combine into a 4, to give
<table>
    <tr>
        <td>4</td><td>4</td><td>_</td><td>_</td>
    </tr>
</table>
Note that there is only one pass: the 4's don't immediately combine into an 8.

It would be very easy represent both these processes as functions on lists in Haskell....


In Idris, we have the possibility to use dependent types, that is types that depend on other types, or integers.  Here, we can use fixed lengths instead of lists.