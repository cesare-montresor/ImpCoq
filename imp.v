Require Import Unicode.Utf8.
Require Import String.
Require Import List.

Section ImpLanguage.

Inductive Loc: Type := LOC: string -> Loc.
Definition storeT := list (Loc * nat).
Check Loc.
Check storeT.

Definition LocEqual (loc1 loc2: Loc) : bool :=
  match loc1 with
  | LOC str => 
    match loc2 with 
    | LOC str' => eqb str str'
    end
  end.

Inductive Aexpr: Set :=
  | N   : nat -> Aexpr
  | VAR : Loc -> Aexpr
  | SUM : Aexpr -> Aexpr -> Aexpr
  | SUB : Aexpr -> Aexpr -> Aexpr
  | MUL : Aexpr -> Aexpr -> Aexpr
.

Inductive Bexpr: Set :=
  | TT
  | FF
  | EQ  : Aexpr -> Aexpr -> Bexpr
  | LEQ : Aexpr -> Aexpr -> Bexpr
  | NOT : Bexpr -> Bexpr
  | AND : Bexpr -> Bexpr -> Bexpr
  | OR  : Bexpr -> Bexpr -> Bexpr
.

Inductive Com: Type :=
  | SKIP
  | SEQ   : Com -> Com -> Com
  | IF    : Bexpr -> Com -> Com -> Com
  | ASS   : Loc -> Aexpr -> Com
  | WHILE : Bexpr -> Com -> Com
.

Notation "A ??" := (option A) (at level 80).
Notation "@ A" := (LOC A) (at level 80).
Notation "A == B" := (LocEqual A B) (at level 80).

Fixpoint readLoc (loc: Loc) (store: storeT) {struct store} : nat??:= 
  match store with
    | (loc',n)::store => if loc==loc' then Some n else readLoc loc store
    | nil => None
  end.

(**
Definition lista := (@"A", 1)::(@"B", 2)::(@"C", 3)::nil.
Compute readLoc (@"A") lista.
Compute readLoc (@"Z") lista.
**)

End ImpLanguage.
