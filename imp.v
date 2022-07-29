Require Import Unicode.Utf8.
Require Import String.
Require Import List.
Require Import ZArith.

Section ImpLanguage.

Inductive Loc: Type := LOC: string -> Loc.
Definition storeT := list (Loc * Z).
Check Loc.
Check storeT.

Definition LocEqual (loc1 loc2: Loc) : bool :=
  match loc1 with
  | LOC str => 
    match loc2 with 
    | LOC str' => eqb str str'
    end
  end.

Inductive Aexpr: Type :=
  | N   : Z -> Aexpr
  | VAR : Loc -> Aexpr
  | SUM : Aexpr -> Aexpr -> Aexpr
  | SUB : Aexpr -> Aexpr -> Aexpr
  | MUL : Aexpr -> Aexpr -> Aexpr
.

Inductive Bexpr: Type :=
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

Fixpoint readLoc (loc: Loc) (store: storeT) {struct store} : Z:= 
  match store with
    | (loc',n)::store' => if LocEqual loc loc' then n else readLoc loc store'
    | nil => 0 (**Stato iniziale**)
  end.
  
Fixpoint assignLocRec (loc: Loc) (head: storeT) (tail: storeT) (n: Z) {struct tail} : storeT:=
  match tail with
    | (currloc,currn)::tail' => if LocEqual currloc loc then app ((loc,n)::head) tail' else assignLocRec loc ((currloc,currn)::head) tail' n
    | nil => (loc,n)::head
  end.
  
Definition assignLoc (loc: Loc) (store: storeT) (n: Z) : storeT:=
  assignLocRec loc nil store n.

(**
Notation "@ A" := (LOC A) (at level 80).
Notation "A == B" := (LocEqual A B) (at level 80).
Definition lista := (@"A", 1)::(@"B", 2)::(@"C", 3)::nil.
Compute readLoc (@"A") lista.
Compute readLoc (@"Z") lista.
**)


Fixpoint evalAexpr (aexpr: Aexpr) (store: storeT) : Z :=
  match aexpr with
    | N n       => n
    | VAR loc   => readLoc loc store
    | SUM e1 e2 => (evalAexpr e1 store) + (evalAexpr e2 store)
    | SUB e1 e2 => (evalAexpr e1 store) - (evalAexpr e2 store)
    | MUL e1 e2 => (evalAexpr e1 store) * (evalAexpr e2 store)
  end.

Fixpoint evalBexpr (bexpr: Bexpr) (store: storeT) : bool :=
  match bexpr with
    | TT        => true
    | FF        => false
    | EQ e1 e2  => Z.eqb (evalAexpr e1 store) (evalAexpr e2 store)
    | LEQ e1 e2 => Z.leb (evalAexpr e1 store) (evalAexpr e2 store)
    | NOT e1    => negb (evalBexpr e1 store)
    | AND e1 e2 => andb (evalBexpr e1 store) (evalBexpr e2 store)
    | OR e1 e2  => orb (evalBexpr e1 store) (evalBexpr e2 store)
  end.
  
Inductive execCommand : Com -> storeT -> storeT -> Prop :=
  | E_SKIP        : forall store: storeT, 
                  execCommand SKIP store store
  | E_ASS         : forall (store: storeT) (exp:Aexpr) (loc: Loc),
                  execCommand (ASS loc exp) store (assignLoc loc store (evalAexpr exp store))
  | E_SEQ         : forall (s s' s'': storeT) (c1 c2: Com),
                  execCommand c1 s s' -> execCommand c2 s' s'' -> execCommand (SEQ c1 c2) s s''
  | E_IF_TRUE     : forall (s s': storeT) (c1 c2: Com) (b: Bexpr),
                  evalBexpr b s = true -> execCommand c1 s s' -> execCommand (IF b c1 c2) s s'
  | E_IF_FALSE    : forall (s s': storeT) (c1 c2: Com) (b: Bexpr),
                  evalBexpr b s = false -> execCommand c2 s s' -> execCommand (IF b c1 c2) s s'
  | E_WHILE_TRUE  : forall (s s': storeT) (c: Com) (b: Bexpr),
                  evalBexpr b s = true -> execCommand c s s' -> execCommand (WHILE b c) s s'
  | E_WHILE_FALSE : forall (s s': storeT) (c: Com) (b: Bexpr),
                  evalBexpr b s = false -> execCommand (WHILE b c) s s
.

Definition equivalence (c1 c2: Com) : Prop :=
  forall (s s': storeT),
    execCommand c1 s s' <-> execCommand c2 s s'.



End ImpLanguage.
