Add LoadPath "~/coqFinal/Sudoku_Coq".
Set Implicit Arguments.
Unset Strict Implicit.
Require Export Sudoku_Engine_Final.
Require Export Sudoku_Game_Repo.

Goal solvable level_0.
Proof.
unfold level_0.
f_1.
f_8.
Qed.

Goal solvable level_2.
Proof.
unfold level_2.
f_6. f_5. f_9. f_8.
f_7. f_4. f_8. f_9. f_3. f_6.
f_9. f_3. f_7. f_1. f_2.
f_3. f_6. f_4. f_5. f_9.
f_1. f_8. f_6. f_2. f_4.
f_7. f_2. f_1. f_4. f_6. f_8.
f_2. f_1. f_5. f_7. f_3.
f_8. f_9. f_2. f_6. f_7. 
f_9. f_7. f_8. f_4. f_3. f_5. f_2. f_1.
Qed.