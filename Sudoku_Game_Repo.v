(*

"Warning!!!"
"Compile each File before Playing the Sudoku Game: Compile -> Compile Buffer"

Name: Sudoku_Game_Repo (a part of Sudoku_Coq, final project of CS386L)

Author: Yaohua Zhao

Date: 2018.04.25

Last Update: 2018.04.25

Total Number of Easy: 6
Total Number of Medium: 3
Total Number of Hard: 3

Description:
This is the Sudoku game repo. The difficulity is indicated with "easy", "medium" and
"hard". There are total 7 questions in the repo. Feel free to add you own Sudoku 
question. But do not forget the cursor indicator "+" and cursor symbol "X".

References: https://www.puzzles.ca/sudoku/

*)

(* add you own path here, which is absolute path *)
Add LoadPath "~/coqFinal/Sudoku_Coq".

Set Implicit Arguments.
Unset Strict Implicit.
Require Export Sudoku_Engine_Final.

(* level_0 is just for tutorial purpose *)
Definition easy_0 :=
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
  .

Definition easy_1 :=
  +> 5 3 X _ 7 _ _ _ _ <|
  |> 6 _ _ 1 9 5 _ _ _ <|
  |> _ 9 8 _ _ _ _ 6 _ <|
  |> 8 _ _ _ 6 _ _ _ 3 <|
  |> 4 _ _ 8 _ 3 _ _ 1 <|
  |> 7 _ _ _ 2 _ _ _ 6 <|
  |> _ 6 _ _ _ _ 2 8 _ <|
  |> _ _ _ 4 1 9 _ _ 5 <|
  |> _ _ _ _ 8 _ _ 7 9 <|
  |><|
  .

Definition easy_2 :=
  +> 1 3 X 2 _ _ 7 4 _ <|
  |> _ 2 5 _ 1 _ _ _ _ <|
  |> 4 8 _ _ 6 _ _ 5 _ <|
  |> _ _ _ 7 8 _ 2 1 _ <|
  |> 5 _ _ _ 9 _ 3 7 _ <|
  |> 9 _ _ _ 3 _ _ _ 5 <|
  |> _ 4 _ _ _ 6 8 9 _ <|
  |> _ 5 3 _ _ 1 4 _ _ <|
  |> 6 _ _ _ _ _ _ _ _ <|
  |><|
  .

Definition easy_3 :=
  +> 1 X _ _ _ _ 2 7 6 <|
  |> _ _ 9 1 4 _ _ _ _ <|
  |> _ 2 _ _ _ 6 _ 9 1 <|
  |> _ 8 _ _ _ 9 6 1 _ <|
  |> 7 3 _ _ 8 4 _ _ _ <|
  |> _ _ 2 _ _ 5 _ 8 _ <|
  |> 5 _ 6 _ _ 3 _ _ _  <|
  |> _ _ 7 _ _ _ _ 5 _ <|
  |> 3 4 _ 5 9 _ _ _ _ <|
  |><|
  .

Definition easy_4 :=
  +> 1 X _ _ _ _ 2 7 6 <|
  |> _ _ 9 1 4 _ _ _ _ <|
  |> _ 2 _ _ _ 6 _ 9 1 <|
  |> _ 8 _ _ _ 9 6 1 _ <|
  |> 7 3 _ _ 8 4 _ _ _ <|
  |> _ _ 2 _ _ 5 _ 8 _ <|
  |> 5 _ 6 _ _ 3 _ _ _ <|
  |> _ _ 7 _ _ _ _ 5 _ <|
  |> 3 4 _ 5 9 _ _ _ _ <|
  |><|
  .

Definition easy_5 :=
  +> 1 X _ _ _ 3 6 _ _ <|
  |> 9 _ _ 6 5 _ _ _ 2 <|
  |> _ _ _ 8 9 _ 3 1 _ <|
  |> _ 2 4 _ 1 5 _ _ _ <|
  |> _ 6 _ 3 _ 7 8 4 _ <|
  |> _ _ _ _ 6 _ _ _ _ <|
  |> _ _ 5 _ _ _ _ _ 6 <|
  |> 6 3 _ 7 _ 9 _ 5 4 <|
  |> _ 9 1 _ _ _ _ 3 _ <|
  |><|
  .

Definition medium_1 :=
  +> 8 9 2 X _ 3 _ 1 4 <|
  |> _ _ _ _ _ _ _ _ _ <|
  |> _ _ _ _ 6 8 _ 7 _ <|
  |> 4 5 _ _ 8 _ _ _ 1 <|
  |> _ _ 8 _ _ _ 2 _ _ <|
  |> 1 _ 3 7 _ _ 5 _ _ <|
  |> _ 7 1 _ _ 6 _ 5 _ <|
  |> 5 _ 9 2 _ _ _ 8 _ <|
  |> 6 _ _ _ _ 7 _ _ 9 <|
  |><|
  .

Definition medium_2 :=
  +> 1 2 3 X 7 _ _ _ _ <|
  |> 5 9 7 3 _ 4 _ _ _ <|
  |> 4 _ _ 9 1 _ _ 3 _ <|
  |> _ _ 2 _ 8 7 5 9 _ <|
  |> _ _ _ 4 _ 9 6 1 _ <|
  |> _ _ _ _ 3 5 _ _ 8 <|
  |> 8 4 _ _ _ 3 _ 5 7 <|
  |> _ _ _ _ _ _ _ _ _ <|
  |> _ 7 _ _ _ _ 9 _ _ <|
  |><|
  .

Definition medium_3 :=
  +> 9 1 2 3 5 X _ _ 7 <|
  |> _ _ 8 _ _ 2 _ 1 _ <|
  |> _ 6 _ 8 _ _ _ _ _ <|
  |> 2 9 _ 5 6 3 1 _ _ <|
  |> _ _ _ _ 1 9 _ 3 _ <|
  |> _ _ _ 2 _ 4 6 _ _ <|
  |> 6 _ _ _ 3 8 _ _ _ <|
  |> _ 3 _ _ _ _ 8 _ 2 <|
  |> _ _ _ 6 _ _ _ 5 9 <|
  |><|
  .

Definition hard_1 :=
  +> 6 X _ _ 9 1 _ _ _ <|
  |> _ 4 _ 7 _ _ _ _ _ <|
  |> 8 _ _ _ _ _ _ 2 3 <|
  |> _ _ 9 _ _ _ 4 8 _ <|
  |> _ _ _ 6 _ 8 _ 5 _ <|
  |> _ 1 _ _ 3 _ _ _ _ <|
  |> _ _ _ _ _ 7 1 _ _ <|
  |> _ 2 _ _ _ _ 6 _ _ <|
  |> _ _ _ _ 6 _ _ _ _ <|
  |><|
  .

Definition hard_2 :=
  +> X _ _ _ _ _ _ 7 5 <|
  |> _ _ 3 _ _ _ 8 _ 9 <|
  |> 4 _ _ _ 8 3 _ _ _ <|
  |> 7 8 _ _ _ 6 _ 1 _ <|
  |> _ _ _ 5 7 _ _ _ _ <|
  |> _ _ _ _ _ _ _ _ 2 <|
  |> _ 3 _ 1 _ _ _ _ 8 <|
  |> _ _ 5 _ _ _ _ _ _ <|
  |> _ 1 9 _ _ _ _ 6 _ <|
  |><|
  .

Definition hard_3 :=
  +> 9 X _ _ _ _ _ _ _ <|
  |> _ _ _ _ 7 8 _ _ _ <|
  |> _ _ 7 _ 9 _ 3 _ 1 <|
  |> _ _ 9 8 _ 5 _ 3 _ <|
  |> 3 _ _ _ _ _ _ 2 4 <|
  |> _ 2 _ _ _ _ _ _ _ <|
  |> 7 _ _ _ _ _ 1 _ _ <|
  |> _ _ 2 _ _ _ 7 _ 6 <|
  |> _ _ 6 1 _ _ _ _ 8 <|
  |><|
  .