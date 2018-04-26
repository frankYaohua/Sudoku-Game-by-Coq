(*

Name: Sudoku_Game_Board (a part of Sudoku_Coq, final project of CS386L)

Author: Yaohua Zhao

Date: 2018.04.25

Last Update: 2018.04.25

Description: This is the start page of the game, or we say the game board.
Here you can retrieve and solve the Sudoku game by the Coq fashion. To be
specific, you set a goal, or we say a Theorem. Then, apply some simple "tactics"
or "constructors", you can prove this goal under the rules of Sudoku.

The "tactics" I provided to you are filling the number in the empty space.
To make the game much more user-friendly, I added a cursor to indicate, 
which empty space you are in right now. After you fill a number in that 
space, the cursor will automatically jump to the next available empty space.

After you have filled all empty space in the given Sudoku question, the coq 
will automatically check whether you have prove this problem under the 
rules of Sudoku, which are "valid in rows", "valid in columns" and 
"valid in subboards". If you are not farmiliar with Sudoku game, what a pity.
Check the introduction here before you start.
https://en.wikipedia.org/wiki/Sudoku

Game Symbols:
+> : The row cursor is currently in.
|> : The normal rows.
X : Cursor.
_ : Empty space needs to be filled.

Game Operations:
Goal solvable "question name" : Load the indicated game.
Theorem "whatever you want" : solvable "question name" : Load the indicated game.
f_1 : Fill number one in the current empty space (in the current cursor).
f_2, f_3, f_4, f_5, f_6, f_7, f_8, f_9.
unfold "question name" : Show the current question board.
Proof. : Start to prove.
Qed. : Finish and close the question.

Question Repo:
The predefined questions can be found in the "Sudoku_Game_Repo.v" file.
Qestion name is: "difficulty_number" e.g. easy_0, medium_1, hard_1.
Total number of questions are shown below.
easy: 0-4
medium: 1-
hard: 1-

*)

(* add you own path here, which is absolute path *)
Add LoadPath "~/coqFinal/Sudoku_Coq".
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Sudoku_Engine_Final.
Require Export Sudoku_Game_Repo.

(* ------------- Tutorial ------------- *)

Goal solvable easy_0. (* load the question easy_0. *)
Proof. (* start to prove *)
(* unfold the game board (optional) highly recommended, you know why :) *)
unfold easy_0.
f_1. (* fill 1 in (1, 1) *)
f_8. (* fill 8 in (9, 9) *)
Qed. (* you success! finish the prove *)
(* or, you can use "Save solution. Print solution." 
to show your steps before "Qed" *)

(* same question, try differently *)
Theorem your_life : solvable easy_0. (* load the question easy_0. *)
Proof. (* start to prove *)
(* unfold the game board (optional) highly recommended, you know why :) *)
unfold easy_0.
f_1. (* fill 1 in (1, 1) *)
f_8. (* fill 8 in (9, 9) *)
Qed. (* look at right console, your life is defined *)

(* --------- End of Tutorial ---------- *)

(* Now, set your own goal and enjoy the game of sudoku *)