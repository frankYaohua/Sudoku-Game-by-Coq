(*

Name: Sudoku_Game_Repo (a part of Sudoku_Coq, final project of CS386L)

Author: Yaohua Zhao

Date: 2018.04.25

Total Number of Levels: XXX

Last Update: 2018.04.25

Description:
This is the Sudoku game repo. The difficulity is increasing with increasing of
the level number. There are total XXX from level_0 to level XXX in the repo.
Feel free to add you own Sudoku question. But do not forget the cursor symbol "+".

References: 

*)

(* add you own path here, which is absolute path *)
Add LoadPath "~/coqFinal/Sudoku_Coq".

Set Implicit Arguments.
Unset Strict Implicit.
Require Export Sudoku_Engine_Final.

(* level_0 is just for tutorial *)
Definition level_0 :=
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

Definition level_1 :=
  +> 5 3 _ _ 7 _ _ _ _ <|
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

Definition level_2 :=
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