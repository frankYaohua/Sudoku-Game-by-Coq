Add LoadPath "~/coqFinal/Sudoku_Coq".
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Sudoku_Engine_Final.
Require Export Sudoku_Game_Repo.

Goal solvable level_1.
Proof.
unfold level_1.
f_7.
f_4.
f_4.
f_3.
f_6.
Save solution.
Print solution.
