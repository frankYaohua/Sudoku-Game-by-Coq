# Sudoku Game by Using Coq Philosophy

The Sudoku game is developed by coq from a mathematical perspective. The Sudoku game is a Goal or Theorem which needs to be proved by using given tactics. The Sudoku project has overall three sections, Sudoku Engine (which provides the basic logic, checks, tactics, and UI of the Sudoku game), Sudoku Game Repo (which stores some of the predefined Sudoku questions from easy mode to hard mode), and Sudoku Game Board (which is the starting page of the game).

[Video Demo](https://www.youtube.com/watch?v=TYWbiGUijEs)

## Getting Started

It will provide you basic environment, tools and operations needed to run the game.

### Prerequisites

Coq IDE installed. Please check [here](https://coq.inria.fr/) for more information.

### Installing

Download the Coq IDE, Copy the repo and then you are good to go.

Copy the repo:
```
git clone https://github.com/frankYaohua/Sudoku_Coq.git
```

Open three .v files and compile -> compile buffer of each of them.

**Deprecated:** (Reference: https://coq.discourse.group/t/add-loadpath-in-coq-8-12-2/1211/4)
Modify the Path to your folder's own absolute path. You can find this line on the nearly top of the files.
```
Add LoadPath "<your own absolute path>". (e.g. Add LoadPath "~/coqFinal/Sudoku_Coq".)
```
**Edit:**
No need to do anything but just compile and run. There is a new `_CoqProject` file handles all of this dependancies for you.


## Running the Tutorial

The tutorial game is in the Sudoku_Game_Board.v file. The instruction there will lead you to play the game. After that, you can load the predefined Sudoku puzzles and even make your own one. Simple operations are listed below.

Set goal:
```
Goal solvable easy_0.
```
Check the question, show the Sudoku board:
```
unfold easy_0.
```
Fill number 1 in the current cursor:
```
f_1.
```
Complete the goal (Actually, the Sudoku Engine will automatically check your answer every time after you fill a number)
```
Qed.
```
(Optional) Save the solution, and look back the steps you did:
```
Save solution. Print solution.
``` 
### Tutorial Question UI Snippet
* X : Cursor
* _ : Empty space
* 1-9 : Prefilled number
* +> : The active row indicator
```
1 subgoal
______________________________________(1/1)
solvable
  +> X 2 3 4 5 6 7 8 9 <|
  |> 4 5 6 7 8 9 1 2 3 <|
  |> 7 8 9 1 2 3 4 5 6 <|
  |> 2 3 4 5 6 7 8 9 1 <|
  |> 5 6 7 8 9 1 2 3 4 <|
  |> 8 9 1 2 3 4 5 6 7 <|
  |> 3 4 5 6 7 8 9 1 2 <|
  |> 6 7 8 9 1 2 3 4 5 <|
  |> 9 1 2 3 4 5 6 7 _ <|
  |><|
```
## Detail of Implementation
Please refer to the code comments for details of the implementations and logics.

## Authors

* **Yaohua Zhao** - [Github](https://github.com/frankYaohua)

Special thanks go to Jasper Stein: <jasper@cs.kun.nl> who provides the abstract structure of coq-developed game I referred to.

## License

This project is licensed under the GNU License - see the [LICENSE](LICENSE) file for details

## Acknowledgments

* Jasper Stein - <jasper@cs.kun.nl> - for ideas and abstract game structure
* [William R. Cook](http://www.cs.utexas.edu/~wcook/) - Professor of the CS386L - for inspirations through the semester
