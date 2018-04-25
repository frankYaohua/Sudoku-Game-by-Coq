Set Implicit Arguments.
Unset Strict Implicit.

(* the basic field of the game board *)
Inductive fieldType : Type :=
  | Empty : fieldType (* the space waits to be filled *)
  | Number : fieldType (* the given number *)
  | Cursor : fieldType  (* the cursor, move it to fill number *)
  | One : fieldType
  | Two : fieldType
  | Three : fieldType
  | Four : fieldType
  | Five : fieldType
  | Six : fieldType
  | Seven : fieldType
  | Eight : fieldType
  | Nine : fieldType.

(* the directions that cursor can move to *)
Inductive Direction : Type :=
  | No : Direction
  | Ea : Direction
  | So : Direction
  | We : Direction
  | Ju : Direction
  | Fi : Direction.

(* define the game board: field, row, board *)
(* Definition mylist := C 1 (C 2 (C 3 nil)). *)
Inductive Row : Type :=
  | nil : Row
  | C : fieldType -> Row -> Row.

(* board is the list of row, including cursor row *)
Inductive Board : Type :=
  | Nothing : Board
  | R : Row -> Board -> Board  (* normal row *)
  | K : Row -> Board -> Board. (* cursor row *)

(* to check if game is over or not, 
you should row ready and column ready *)

(* =================== Board Row CODE =================== *)

Inductive numList : Type :=
  | E : numList
  | L : fieldType -> numList -> numList.

Definition myList := 
(L One (L Two (L Three (L Four (L Five (L Six (L Seven (L Eight (L Nine E))))))))).

Definition isEmpty (l : numList) : Prop :=
match l with
  | E => True
  | _ => False
end.

Definition isSame (f : fieldType) (x : fieldType) : bool :=
match f, x with
  | One, One | Two, Two | Three, Three | Four, Four | Nine, Nine => true
  | Five, Five | Six, Six | Seven, Seven | Eight, Eight => true
  | _, _ => false
end.

Fixpoint removeElement (f : fieldType) (l : numList) : numList :=
match l with
  | E => E
  | L x Ls => 
    match (isSame f x) with
      | true => Ls
      | false => L x (removeElement f Ls)
    end
  end.

Fixpoint rowReady (r : Row) (l : numList) : Prop :=
match r with
  | nil => isEmpty l
  | C x xs => rowReady xs (removeElement x l)
end.



Fixpoint boardRowReady (b : Board) : Prop :=
match b with
  | Nothing => True
  | R r rs => rowReady r myList /\ boardRowReady rs
  | K r rs => rowReady r myList /\ boardRowReady rs
end.


(* ================== Board Col CODE ====================== *)


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


Fixpoint getNthColList (b : Board) (n : nat) : numList :=
match b with
  | Nothing => E
  | R r b' => L (getNthElement (r) (n)) (getNthColList b' n)
  | K r b' => L (getNthElement (r) (n)) (getNthColList b' n)
end.

Fixpoint listReady (col : numList) (l : numList) : Prop :=
match col with
  | E => isEmpty l
  | L f col' => listReady col' (removeElement f l)
end.


Definition boardNthColReady (b : Board) (n : nat) : Prop :=
match b with
  | Nothing => True
  | R r rs => listReady (getNthColList (R r rs) n) (myList)
  | K r rs => listReady (getNthColList (R r rs) n) (myList)
end.


Fixpoint boardColReady (b : Board) (n : nat) : Prop :=
match n with
  | O => boardNthColReady b O
  | S n' => boardNthColReady b n' /\ boardColReady b n'
end.


(* ================= FINAL RULE (NO USE) =============== *)

Definition boardReady (b : Board) : Prop :=
boardColReady b 9.


(* =============== CELL READY CODE ================= *)

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

Fixpoint appendList (l1 : numList) (l2 : numList) : numList :=
  match l1 with
  | E => l2
  | L x l1' => L x (appendList l1' l2)
  end.

Definition getSnippet (b : Board) (r n1 n2 n3 : nat) : numList :=
  L (getNthElement (getNthRow b r) n3) 
  (L (getNthElement (getNthRow b r) n2) 
  (L (getNthElement (getNthRow b r) n1) E)).

Definition getCellList (b : Board) (r1 r2 r3 c1 c2 c3: nat) : numList :=
appendList (getSnippet b r1 c1 c2 c3) 
(appendList (getSnippet b r2 c1 c2 c3) (getSnippet b r3 c1 c2 c3)).

(*
Fixpoint boardColReady (b : Board) (n : nat) : Prop :=
match n with
  | O => boardNthColReady b O
  | S n' => boardNthColReady b n' /\ boardColReady b n'
end.
*)


Definition boardNthCellReady (b : Board) (l : numList) : Prop :=
match b with
  | Nothing => True
  | R r rs => listReady (l) (myList)
  | K r rs => listReady (l) (myList)
end.

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

Fixpoint boardCellReady (b : Board) (n : nat) : Prop :=
match n with
  | O => boardNthCellReady b (getCode b 0)
  | S n' => boardNthCellReady b (getCode b n') /\ boardCellReady b n'
end.


(*listReady (getCellList b 0 1 2 0 1 2) (myList).*)


(* ================= FINAL RULE =============== *)

(* define a rule *)

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

(* move the cursor east and west *)
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

(* the actual step function *)
Fixpoint stepeast (b : Board) : Board :=
match b with
  | K r b' => K (rowstepeast r) b'
  | R r b' => R r (stepeast b')
  | Nothing => Nothing
end.

Fixpoint stepwest (b : Board) : Board :=
match b with
  | K r b' => K (rowstepwest r) b'
  | R r b' => R r (stepwest b')
  | Nothing => Nothing
end.


(* ================= CODE TO FILL ===================== *)

Fixpoint hasEmptyInThisRow (r : Row) : bool :=
match r with
  | C x r' => 
    match x with
    | Empty => true
    | _ => hasEmptyInThisRow r'
    end
  | _ => false
end.

Fixpoint changeFirstEmptyToCursorInRow (r : Row) : Row :=
match r with
  | C x rs =>
    match x with
    | Empty => C Cursor rs
    | _ => C x (changeFirstEmptyToCursorInRow rs)
    end
  | nil => nil
  end.

Fixpoint changeFirstEmptyToCursorInBoard (b : Board) : Board :=
match b with
  | R r b' => 
    match (hasEmptyInThisRow r) with
    | false => R r (changeFirstEmptyToCursorInBoard b')
    | true => K (changeFirstEmptyToCursorInRow r) b'
    end
  | _ => Nothing
  end.

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


Fixpoint changeFirstCursorToNumber (f : fieldType) (r : Row) : Row :=
match r with
  | C x rs =>
    match x with
    | Cursor => C f rs
    | _ => C x (changeFirstCursorToNumber f rs)
    end
  | nil => nil
  end.

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

(* This one's command: 
No north and south first *)
Definition dostep (r : Direction) (b : Board) : Board :=
match r with
  | Ea => stepeast b
  | We => stepwest b
  | _ => stepeast b
end.

Inductive solvable : Board -> Prop :=
  | OK : forall b : Board, boardRowReady b -> 
    boardColReady b 9 -> boardCellReady b 9 -> solvable b
  (* for debugging only *)
  | CELL : forall b : Board, boardCellReady b 9 -> solvable b

  | STEP :
      forall (b : Board) (d : Direction), solvable (dostep d b) -> solvable b
  | FILLNUMBER :
      forall (b : Board) (f : fieldType), 
      solvable (fill f b) -> solvable b.


(* Four tactics to play the game easier: *)
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


(* Notations *)
Notation "'_' a" := (C Empty a) (at level 0, right associativity).

Notation "'X' a" := (C Cursor a) (at level 0, right associativity).
Notation "'F' a" := (C Number a) (at level 0, right associativity).

Notation "<|" := nil (at level 0).

Notation "|> a b" := (R a b)
  (format "'[v' |>  a '/' b ']'", at level 0, a, b at level 0).
Notation "+> a b" := (K a b)
  (format "'[v' +>  a '/' b ']'", at level 0, a, b at level 0).
Notation "|><|" := Nothing (format "|><| '//'", at level 0).

Notation "'1' a" := (C One a) (at level 0, right associativity).
Notation "'2' a" := (C Two a) (at level 0, right associativity).
Notation "'3' a" := (C Three a) (at level 0, right associativity).
Notation "'4' a" := (C Four a) (at level 0, right associativity).
Notation "'5' a" := (C Five a) (at level 0, right associativity).
Notation "'6' a" := (C Six a) (at level 0, right associativity).
Notation "'7' a" := (C Seven a) (at level 0, right associativity).
Notation "'8' a" := (C Eight a) (at level 0, right associativity).
Notation "'9' a" := (C Nine a) (at level 0, right associativity).

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

Goal solvable b.
Proof.
unfold b in |- *.
f_7.
f_4.
f_4.
f_3.
f_6.
Save solution'_b.
Print solution'_b. (* Look at the start of this term! *)









