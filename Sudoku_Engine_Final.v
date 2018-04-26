(*

Name: Sudoku_Engine_Final (a part of Sudoku_Coq, final project of CS386L)

Author: Yaohua Zhao

Date: 2018.04.25

Last Update: 2018.04.25

Description: This is the game engine for the coq Sudoku game, the abstract
structure is based on the Github/coq-contribs/Coqoban, 
which is a "push box" game implemented by Coq. Thanks! Appreciate that!

The Sudoku game engine includes: 
- Sudoku Setting
  + Fields
    * Empty
    * Number
    * Cursor
  + Row (list of fields)
  + Board (list of rows)
- Sudoku Game UI
  + Border
  + Empty
  + Number
  + Cursor
  + Cursor Indicator
- Sudoku Cursor Auto-Jumping Logic
  + Jump to next empty in same row
  + Jump to next empty in different row
- Sudoku Operation Tactics
  + Fill Number (1-9)
- Sudoku Solution Checker
  + Sudoku Logic Checker 
    (a list of 9 fields, check if only has 9 unique numbers)
  + Row Checker
  + Column Checker
  + Subboard Checker
- A Simple Test Game

*)

Set Implicit Arguments.
Unset Strict Implicit.

(* ---------- Sudoku Setting ---------- *)

(* the basic type of each cell including empty, cursor and numbers *)
Inductive fieldType : Type :=
  | Empty : fieldType (* the space waits to be filled *)
  | Number : fieldType (* the given number, for initial development purpose *)
  | Cursor : fieldType (* the cursor, indicating the current location *)
  (* number 1-9 as fieldtype *)
  | One : fieldType
  | Two : fieldType
  | Three : fieldType
  | Four : fieldType
  | Five : fieldType
  | Six : fieldType
  | Seven : fieldType
  | Eight : fieldType
  | Nine : fieldType.

(* row in the game board is a list of field type *)
Inductive Row : Type :=
  | nil : Row
  | C : fieldType -> Row -> Row.

(* board in the Sudoku world is a list of row, including cursor row *)
Inductive Board : Type :=
  | Nothing : Board
  | R : Row -> Board -> Board  (* normal row *)
  | K : Row -> Board -> Board. (* row with cursor, for UI purpose *)

(* ---------- Basic Checking Helper Functions ---------- *)

(* manually define a list storing fieldType only *)
Inductive numList : Type :=
  | E : numList
  | L : fieldType -> numList -> numList.

(* myList is a set of 9 unique numbers from 1 to 9, for checking purpose *)
Definition myList := 
(L One (L Two (L Three (L Four (L Five (L Six (L Seven (L Eight (L Nine E))))))))).

(* isEmpty will check if the given list is empty or not, for checking purpose *)
Definition isEmpty (l : numList) : Prop :=
match l with
  | E => True
  | _ => False
end.

(* isSame will compare two fieldtypes whether they are same *)
Definition isSame (f : fieldType) (x : fieldType) : bool :=
match f, x with
  | One, One | Two, Two | Three, Three | Four, Four | Nine, Nine => true
  | Five, Five | Six, Six | Seven, Seven | Eight, Eight => true
  | _, _ => false
end.

(* removeElement will remove all given fieldTypes from given numList *)
Fixpoint removeElement (f : fieldType) (l : numList) : numList :=
match l with
  | E => E
  | L x Ls => 
    match (isSame f x) with
      | true => Ls
      | false => L x (removeElement f Ls)
    end
  end.

(* ---------- Row Checker ---------- *)

(* check if the given row only has 9 unique numbers *)
Fixpoint rowReady (r : Row) (l : numList) : Prop :=
match r with
  | nil => isEmpty l
  | C x xs => rowReady xs (removeElement x l)
end.

(* check if all 9 rows in game board are valid *)
Fixpoint boardRowReady (b : Board) : Prop :=
match b with
  | Nothing => True
  | R r rs => rowReady r myList /\ boardRowReady rs
  | K r rs => rowReady r myList /\ boardRowReady rs
end.

(* ---------- Column Checker with Helper Functions ---------- *)

(* get nth element of the given row *)
Fixpoint getNthElement (r : Row) (n : nat) : fieldType :=
match n with
  | O => match r with
          | C x xs => x
          | nil => Empty (* never in this clause *)
          end
  | S(b) => match r with
          | C x xs => getNthElement xs (b)
          | nil => Empty (* never in this clause *)
          end
  end.

(* get the nth column and construct it into numList of the game board *)
Fixpoint getNthColList (b : Board) (n : nat) : numList :=
match b with
  | Nothing => E
  | R r b' => L (getNthElement (r) (n)) (getNthColList b' n)
  | K r b' => L (getNthElement (r) (n)) (getNthColList b' n)
end.

(* if the given list if valid *)
Fixpoint listReady (col : numList) (l : numList) : Prop :=
match col with
  | E => isEmpty l
  | L f col' => listReady col' (removeElement f l)
end.

(* if the nth column of the given game board is valid *)
Definition boardNthColReady (b : Board) (n : nat) : Prop :=
match b with
  | Nothing => True
  | R r rs => listReady (getNthColList (R r rs) n) (myList)
  | K r rs => listReady (getNthColList (R r rs) n) (myList)
end.

(* if all 9 columns of the given game board are valid *)
Fixpoint boardColReady (b : Board) (n : nat) : Prop :=
match n with
  | O => boardNthColReady b O
  | S n' => boardNthColReady b n' /\ boardColReady b n'
end.

(* ---------- Subboard (Cell) Checker with Helper Functions ---------- *)

(* get nth row of the given board *)
Fixpoint getNthRow (b : Board) (n : nat) : Row :=
match n with
  | O => match b with
        | R r b' => r
        | K r b' => r
        | Nothing => nil
        end
  | S(n') => match b with
            | R r b' => getNthRow b' n'
            | K r b' => getNthRow b' n'
            | Nothing => nil
            end
  end.

(* manually construct the function to append two given lists *)
Fixpoint appendList (l1 : numList) (l2 : numList) : numList :=
  match l1 with
  | E => l2
  | L x l1' => L x (appendList l1' l2)
  end.

(* get the n1, n2, n3 elements of the given row and construct to list *)
Definition getSnippet (b : Board) (r n1 n2 n3 : nat) : numList :=
  L (getNthElement (getNthRow b r) n3) 
  (L (getNthElement (getNthRow b r) n2) 
  (L (getNthElement (getNthRow b r) n1) E)).

(* 
get the subboard with the detailed location information.
r1 r2 r3 are the row number, c1 c2 c3 are the column number.
Which locate to a 3*3 subboard, I called Cell here.
 *)
Definition getCellList (b : Board) (r1 r2 r3 c1 c2 c3: nat) : numList :=
appendList (getSnippet b r1 c1 c2 c3) 
(appendList (getSnippet b r2 c1 c2 c3) (getSnippet b r3 c1 c2 c3)).

(* there are overall 9 subboards in the game boards, get the nth subboard *)
Definition boardNthCellReady (b : Board) (l : numList) : Prop :=
match b with
  | Nothing => True
  | R r rs => listReady (l) (myList)
  | K r rs => listReady (l) (myList)
end.

(* each subboard has a unique r1 r2 r3 c1 c2 c3 code for simplicity purpose *)
Definition getCode (b : Board) (n : nat) : numList :=
match n with
  | 0 => getCellList b 0 1 2 0 1 2
  | 1 => getCellList b 3 4 5 0 1 2
  | 2 => getCellList b 6 7 8 0 1 2
  | 3 => getCellList b 0 1 2 3 4 5
  | 4 => getCellList b 3 4 5 3 4 5
  | 5 => getCellList b 6 7 8 3 4 5
  | 6 => getCellList b 0 1 2 6 7 8
  | 7 => getCellList b 3 4 5 6 7 8
  | 8 => getCellList b 6 7 8 6 7 8
  | _ => getCellList b 0 1 2 0 1 2
end.

(* check if all 9 subboards of the game board are valid *)
Fixpoint boardCellReady (b : Board) (n : nat) : Prop :=
match n with
  | O => boardNthCellReady b (getCode b 0)
  | S n' => boardNthCellReady b (getCode b n') /\ boardCellReady b n'
end.

(* ---------- Cursor Auto-Jumping Logic ---------- *)

(* check if the given row has empty space *)
Fixpoint hasEmptyInThisRow (r : Row) : bool :=
match r with
  | C x r' => 
    match x with
    | Empty => true
    | _ => hasEmptyInThisRow r'
    end
  | _ => false
end.

(* change the first empty space in the given row to cursor *)
Fixpoint changeFirstEmptyToCursorInRow (r : Row) : Row :=
match r with
  | C x rs =>
    match x with
    | Empty => C Cursor rs
    | _ => C x (changeFirstEmptyToCursorInRow rs)
    end
  | nil => nil
  end.

(* 
change the first empty space in the given board to cursor.
you will find which is helpful, after filling a number and
no more space in the current row
 *)
Fixpoint changeFirstEmptyToCursorInBoard (b : Board) : Board :=
match b with
  | R r b' => 
    match (hasEmptyInThisRow r) with
    | false => R r (changeFirstEmptyToCursorInBoard b')
    | true => K (changeFirstEmptyToCursorInRow r) b'
    end
  | _ => Nothing
  end.

(* 
the current row has cursor and empty, 
then, change cursor to the given fieldType and 
change the empty space after the previous cursor to cursor.
*)
Fixpoint changeFirstCursorToNumberAndEmptyToCursorInRow 
(f : fieldType) (r : Row) : Row :=
match r with
  | C x rs =>
    match x with
    | Cursor => C f (changeFirstEmptyToCursorInRow rs)
    | _ => C x (changeFirstCursorToNumberAndEmptyToCursorInRow f rs)
    end
  | nil => nil
  end.

(* 
just change the cursor to the given number.
this is because the next available empty space is not in the current row
 *)
Fixpoint changeFirstCursorToNumber (f : fieldType) (r : Row) : Row :=
match r with
  | C x rs =>
    match x with
    | Cursor => C f rs
    | _ => C x (changeFirstCursorToNumber f rs)
    end
  | nil => nil
  end.

(* 
fill number right at the cursor place, and then we face two situations
- the current cursor row has empty space -> put it with cursor
- the current cursor row does not have empty space -> find next availble empty space,
  and fill with cursor
*)
Fixpoint fill (f : fieldType) (b : Board) : Board :=
match b with
  | R r b' => R r (fill f b')
  | K r b' => 
    match (hasEmptyInThisRow r) with
    | true => K (changeFirstCursorToNumberAndEmptyToCursorInRow f r) b'
    | false => R (changeFirstCursorToNumber f r) (changeFirstEmptyToCursorInBoard b')
    end
  | Nothing => Nothing
end.

(* ---------- apply the Sudoku Game Rules ---------- *)

(* 
It only has two simple constructors (approaches),
- the board is valid
- fill a number to make it valid
*)
Inductive solvable : Board -> Prop :=
  (* OK: the given board is solvable when row, col and cell are all proved *)
  | OK : forall b : Board, boardRowReady b -> 
    boardColReady b 9 -> boardCellReady b 9 -> solvable b
  (* FILLNUMBER: fill a number, that's tricky. *)
  | FILLNUMBER :
      forall (b : Board) (f : fieldType), 
      solvable (fill f b) -> solvable b.

(* ---------- simplify the game operation ---------- *)

(* 
after fill number, it automatically applies simpl, 
and try if it is OK? 
and apply tauto:
solves goals consisting of tautologies that hold in constructive logic.
*)
Ltac f_1 :=
  apply FILLNUMBER with One; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac f_2 :=
  apply FILLNUMBER with Two; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac f_3 :=
  apply FILLNUMBER with Three; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac f_4 :=
  apply FILLNUMBER with Four; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac f_5 :=
  apply FILLNUMBER with Five; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac f_6 :=
  apply FILLNUMBER with Six; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac f_7 :=
  apply FILLNUMBER with Seven; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac f_8 :=
  apply FILLNUMBER with Eight; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac f_9 :=
  apply FILLNUMBER with Nine; simpl in |- *; try (apply OK; simpl in |- *; tauto).

(* ---------- Notation to make Game UI ---------- *)

(* indicate empty space *)
Notation "'_' a" := (C Empty a) (at level 0, right associativity).
(* indicate Cursor *)
Notation "'X' a" := (C Cursor a) (at level 0, right associativity).
(* indicate Number, for development purpose only *)
Notation "'F' a" := (C Number a) (at level 0, right associativity).
(* right border of the game board *)
Notation "<|" := nil (at level 0).
(* left border with field type indicating the normal row *)
Notation "|> a b" := (R a b)
  (format "'[v' |>  a '/' b ']'", at level 0, a, b at level 0).
(* left border with field type, and indicating the cursor row *)
Notation "+> a b" := (K a b)
  (format "'[v' +>  a '/' b ']'", at level 0, a, b at level 0).
(* end of the game board *)
Notation "|><|" := Nothing (format "|><| '//'", at level 0).
(* for simplicity purpose, show 1 instead of ONE *)
Notation "'1' a" := (C One a) (at level 0, right associativity).
Notation "'2' a" := (C Two a) (at level 0, right associativity).
Notation "'3' a" := (C Three a) (at level 0, right associativity).
Notation "'4' a" := (C Four a) (at level 0, right associativity).
Notation "'5' a" := (C Five a) (at level 0, right associativity).
Notation "'6' a" := (C Six a) (at level 0, right associativity).
Notation "'7' a" := (C Seven a) (at level 0, right associativity).
Notation "'8' a" := (C Eight a) (at level 0, right associativity).
Notation "'9' a" := (C Nine a) (at level 0, right associativity).

(* ---------- A Example Game ---------- *)

Definition b :=
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

(* the detail about how to play, please check the Sudoku_Game_Board file *)

Goal solvable b.
Proof.
unfold b in |- *.
f_7.
f_4.
f_4.
f_3.
f_6.
Qed.

(* ---------- Legacy Code ---------- *)

(*

The code below was designed for the move of cursor. It has four directions
up, down, left, right indicated by north, south, west and east. The code was 
working actually, I tried and found that it is not user-friendly. So, after 
that I decided to use automatically-jump cursor.

*)

(* the directions that cursor can move to, like your mouse *)
Inductive Direction : Type :=
  | No : Direction
  | Ea : Direction
  | So : Direction
  | We : Direction
  | Ju : Direction
  | Fi : Direction.

(* the legacy way to move a cursor *)
Record rule : Type := mkRule {x1 : fieldType; x2 : fieldType}.

(* can fill the number or not *)
Inductive Can : Type :=
  | CAN : rule -> Can
  | CANT : Can.

(* rule for move the cursor *)
Definition move (r : rule) : Can :=
match r with
  | mkRule Cursor Empty => CAN (mkRule Empty Cursor)
  | _ => CANT
end.

(* switch the element in the list *)
Fixpoint rowstepeast (r : Row) : Row :=
match r with
  | C x rs =>
      match rs with
      | C y ys => 
        match move (mkRule x y) with
        | (* so far, the x and y switch *) CAN (mkRule x' y') => C x' (C y' ys)
        | CANT => C x (rowstepeast rs)
        end
      | _ => r
      end
  | nil => nil
end.

(* switch the element in the list *)
Fixpoint rowstepwest (r : Row) : Row :=
match r with
  | C x rs =>
      match rs with
      | C y ys => 
        match move (mkRule y x) with
        | CAN (mkRule y' x') => C x' (C y' ys)
        | CANT => C x (rowstepwest rs)
        end
      | _ => r
      end
  | nil => nil
end.

(* the actual step east *)
Fixpoint stepeast (b : Board) : Board :=
match b with
  | K r b' => K (rowstepeast r) b'
  | R r b' => R r (stepeast b')
  | Nothing => Nothing
end.

(* the actual step west *)
Fixpoint stepwest (b : Board) : Board :=
match b with
  | K r b' => K (rowstepwest r) b'
  | R r b' => R r (stepwest b')
  | Nothing => Nothing
end.

(* the actual do step function *)
Definition dostep (r : Direction) (b : Board) : Board :=
match r with
  | Ea => stepeast b
  | We => stepwest b
  | _ => stepeast b
end.

(* after each do step, try solvable *)
Inductive solvable_legacy : Board -> Prop :=
  | STEP :
      forall (b : Board) (d : Direction), 
      solvable_legacy (dostep d b) -> solvable_legacy b.

(* tactics to move cursor, jump and fill *)
Ltac n :=
  apply STEP with No; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac e :=
  apply STEP with Ea; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac s :=
  apply STEP with So; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac w :=
  apply STEP with We; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac j :=
  apply STEP with Ju; simpl in |- *; try (apply OK; simpl in |- *; tauto).
Ltac f :=
  apply STEP with Fi; simpl in |- *; try (apply OK; simpl in |- *; tauto).


