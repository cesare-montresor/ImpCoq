Require Import Unicode.Utf8.
Require Import String.
Require Import List.

Section ImpLanguage.

Inductive Loc: Type := LOC: string -> Loc.
Check Loc.

Fixpoint LocEqual (loc1 loc2: Loc) : bool :=
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

Fixpoint readLoc (loc: Loc) (states: list (Loc * nat)) : nat := 
  match states with
    | (loc',n)::states => if LocEqual loc loc' then n else readLoc loc states
    | nil => 0
  end.

(**
Definition lista := (LOC "A", 1)::(LOC "B", 2)::(LOC "C", 3)::nil.
Compute readLoc (LOC "A") lista.
Compute readLoc (LOC "Z") lista.
**)

End ImpLanguage.
