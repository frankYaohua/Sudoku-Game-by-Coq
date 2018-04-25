(* add you own path here, which is absolute path *)
Add LoadPath "~/coqFinal/Sudoku_Coq".

Set Implicit Arguments.
Unset Strict Implicit.
Require Export Sudoku_Engine_Final.

Definition level_1 :=
  |> 5 3 4 6 7 8 9 1 2 <|
  +> 6 X 2 1 9 5 3 4 8 <|
  |> 1 9 8 3 4 2 5 6 7 <|
  |> 8 5 9 7 6 1 4 2 3 <|
  |> 4 2 6 8 5 3 7 9 1 <|
  |> 7 1 3 9 2 _ 8 5 6 <|
  |> 9 6 1 5 3 7 2 8 _ <|
  |> 2 8 7 4 1 9 6 3 5 <|
  |> _ 4 5 2 8 _ 1 7 9 <|
  |><|
  .