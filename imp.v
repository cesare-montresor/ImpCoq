Require Import Unicode.Utf8.
Require Import String.
Require Import List.
Require Import ZArith.

Open Scope Z.

Section ImpLanguage.

(** * Store
      Lo store rappresenta la memoria del programma, viene realizzato utilizzando liste di coppie locazione, intero.
      Abbiamo scelto di implementare le locazioni come un nuovo tipo con un solo costruttore LOC,
      che data una stringa costruisce una locazione.
 *)
 
(** Costruttore per il tipo Loc *)
Inductive Loc: Type := LOC: string -> Loc.

(** Definiamo per semplicità il tipo dello store come una abbreviazione di lista (Loc,Z). *)
Definition storeT := list (Loc * Z).

(** Definiamo inoltre una funzione che calcola se due locazioni sono uguali, cioè se hanno
    lo stesso nome. Per fare questo estraiamo le stringhe dalle due locazioni e le confrontiamo
    con la funzione di uguaglianza tra stringhe. *)
Definition locEq (loc1 loc2: Loc) : bool :=
  match loc1 with
    LOC str => 
    match loc2 with 
      LOC str' => eqb str str' 
    end
  end.
  
(** Questa funzione ricorsiva, data una locazione, restituisce il valore presente nello store
    associato a quella locazione. Per fare questo controlla lo store una coppia alla volta:
    se la prima locazione è uguale a quella che ci interessa restituisce il valore, altrimenti
    richiama la stessa funzione sul resto della lista.
    Se la locazione richiesta non viene trovata restituisce zero, perchè nel testo del progetto ogni store
    contiene tutte le possibili variabili inizializzate a zero.*)
Fixpoint readLoc (loc: Loc) (store: storeT) {struct store} : Z:= 
  match store with
    | (loc',n)::store' => 
        if locEq loc loc' then n else readLoc loc store'
    | nil => 0 (*stato iniziale*)
  end.


(** Questa funzione viene richiamata da assignLoc e effettua l'aggiornamento dello store ricorsivamente.
    Scorre la lista cercando la locazione indicata, se la trova, 
    sostituisce la coppia con una nuova coppia (loc, val). 
    Se non trova la location si limita ad aggiungera la nuova coppia.
    In ogni momento tiene in memoria la parte precedente e successiva alla coppia corrente,
    in modo da poter ricomporre correttamente lo store.
*)
Fixpoint assignLocRec (loc: Loc) (head: storeT) (tail: storeT) (n: Z) {struct tail} : storeT:=
  match tail with
    | (currloc,currn)::tail' => 
        if locEq currloc loc then 
            app ((loc,n)::head) tail' 
        else 
          assignLocRec loc ((currloc,currn)::head) tail' n
    | nil => (loc,n)::head
  end.

(** Questa funzione serve per modificare il valore di una locazione nello store.
    Richiama la sua implementazione assignLocRec.
*)
Definition assignLoc (loc: Loc) (store: storeT) (n: Z) : storeT:=
  assignLocRec loc nil store n.


(** Test delle funzioni implementate *)

Definition mem := ( (LOC "A"), 1)::( (LOC "B"), 2)::( (LOC "C"), 3)::nil.
Compute readLoc (LOC "A") mem.
Definition mem2 := assignLoc (LOC "A") mem 2.
Compute readLoc (LOC "A") mem2.
Compute readLoc (LOC "B") mem2.
Reset mem. Reset mem2.


(** * Sintassi di IMP
     In questa sezione definiamo i tipi induttivi del nostro linguaggio:
     le espressioni aritmetiche, le espressioni booleane e i comandi.
     Ogni costruttore definisce una espressione o un comando diverso.
*)

(**  Espressioni Aritmetiche *)
(** _a := n | var | a0 + a1 | a0 - a1 | a0 * a1_ *)

Inductive Aexpr: Type :=
  | N   : Z -> Aexpr
  | VAR : Loc -> Aexpr
  | SUM : Aexpr -> Aexpr -> Aexpr
  | SUB : Aexpr -> Aexpr -> Aexpr
  | MUL : Aexpr -> Aexpr -> Aexpr
.

(** Espressioni Booleane *)
(** _b := true | false | a0 == a1 | a0 ≤ a1 | ¬ b | b0 ∧ b1 | b0 ∨ b1_ *)

Inductive Bexpr: Type :=
  | TT   
  | FF  
  | EQ  : Aexpr -> Aexpr -> Bexpr
  | LEQ : Aexpr -> Aexpr -> Bexpr
  | NOT : Bexpr -> Bexpr
  | AND : Bexpr -> Bexpr -> Bexpr
  | OR  : Bexpr -> Bexpr -> Bexpr
.

(** Comandi
$ c := skip | X := a | c_0;c_1 | if \ b \ then \ c_0 \ else \ c_1 | while \ b \ do \ c $
*)

Inductive Com: Type :=
  | SKIP
  | ASS   : Loc -> Aexpr -> Com
  | SEQ   : Com -> Com -> Com
  | IF    : Bexpr -> Com -> Com -> Com
  | WHILE : Bexpr -> Com -> Com
.

(** * Sematica di IMP *)

(** Semantica operazionale delle espressioni aritmentiche 
*)
Fixpoint evalAexpr (aexpr: Aexpr) (store: storeT) : Z :=
  match aexpr with
    | N n       => n
    | VAR loc   => readLoc loc store
    | SUM e1 e2 => (evalAexpr e1 store) + (evalAexpr e2 store)
    | SUB e1 e2 => (evalAexpr e1 store) - (evalAexpr e2 store)
    | MUL e1 e2 => (evalAexpr e1 store) * (evalAexpr e2 store)
  end.

(** Semantica operazionale delle espressioni booleane. 
*)
Fixpoint evalBexpr (bexpr: Bexpr) (store: storeT) : bool :=
  match bexpr with
    | TT        => true
    | FF        => false
    | EQ e1 e2  => (Z.eqb (evalAexpr e1 store) (evalAexpr e2 store))
    | LEQ e1 e2 => (Z.leb (evalAexpr e1 store) (evalAexpr e2 store))
    | NOT e1    => negb (evalBexpr e1 store)
    | AND e1 e2 => andb (evalBexpr e1 store) (evalBexpr e2 store)
    | OR e1 e2  => orb (evalBexpr e1 store) (evalBexpr e2 store)
  end.
(** Semantica operazionale dell'esecuzione dei comandi.
*)
Inductive execCommand : Com -> storeT -> storeT -> Prop :=
  | E_SKIP        : forall store: storeT, 
                      execCommand SKIP store store
  | E_ASS         : forall (store: storeT) (exp:Aexpr) (loc: Loc),
                      execCommand (ASS loc exp) store (assignLoc loc store (evalAexpr exp store))
  | E_SEQ         : forall (s s' s'': storeT) (c1 c2: Com),
                      execCommand c1 s s'            ->
                      execCommand c2 s' s''          ->
                      execCommand (SEQ c1 c2) s s''
  | E_IF_TRUE     : forall (s s': storeT) (c1 c2: Com) (b: Bexpr),
                      evalBexpr b s = true           ->
                      execCommand c1 s s'            ->
                      execCommand (IF b c1 c2) s s'
  | E_IF_FALSE    : forall (s s': storeT) (c1 c2: Com) (b: Bexpr),
                      evalBexpr b s = false          ->
                      execCommand c2 s s'            ->
                      execCommand (IF b c1 c2) s s'
  | E_WHILE_TRUE  : forall (s s' s'': storeT) (c: Com) (b: Bexpr),
                      evalBexpr b s = true           ->
                      execCommand c s s''            ->
                      execCommand (WHILE b c) s'' s' ->
                      execCommand (WHILE b c) s s'
  | E_WHILE_FALSE : forall (s: storeT) (c: Com) (b: Bexpr),
                      evalBexpr b s = false -> 
                      execCommand (WHILE b c) s s
.
(** Equivalenza fra comandi *)
Definition comEq (c1 c2: Com) : Prop :=
  forall (s s': storeT),
    execCommand c1 s s' <-> execCommand c2 s s'.


End ImpLanguage.

(** * Theorems*)

Section Teoremi.

  
  Section Teorema_1.
    Axiom b: Bexpr.
    Axiom c: Com.
    
    Definition w  := WHILE b c.
    Definition w' := IF b (SEQ c w) SKIP.
    
    Theorem unroll_while : comEq w w'.
    Proof.
    unfold comEq.
    unfold w'.
    unfold w.
    intros.
    split.
    - intro. inversion H.
      + apply E_IF_TRUE. assumption.
        apply E_SEQ with (s':=s''); assumption.
      + apply E_IF_FALSE. assumption. constructor.
    - intro. inversion H.
      + inversion H6. subst.
        apply E_WHILE_TRUE with (s'':=s'1); assumption.
      + inversion H6. subst.
        apply E_WHILE_FALSE; assumption.
    Qed.
  End Teorema_1.


  Section Teorema_2.
    Definition x := (LOC "x").
    Definition y := (LOC "y").
    Definition var_x := (VAR x).
    Definition var_y := (VAR y).
    
    (* README: LISTA ATTRAVERSO LE ASSIGN CREA PROBLEMI NELLA DIMOSTRAZIONE, LA CONCATENAZIONE FUNZIONA*)
    
    (*
    Definition initStore (store: storeT) := assignLoc y ( assignLoc x store 2 ) 3.
    Definition finalStore (store: storeT) := assignLoc y ( assignLoc x store 0 ) 12.
    *)
    Definition initStore (store: storeT) := ( x, 2%Z )::( y, 3%Z)::store.
    Definition finalStore (store: storeT) := ( x, 0%Z )::( y, 12%Z)::store.
    
    Definition prog := 
      WHILE (LEQ (N 1) var_x ) 
      ( SEQ 
        ( ASS y (MUL var_y (N 2) ) )
        ( ASS x (SUB var_x (N 1) ) )
      ).
    
    Theorem while_step : 
      forall s:storeT, exists s':storeT, 
        execCommand prog (initStore s) s'.
    Proof.
      unfold prog.
      intros.
      exists (finalStore s). 
      eapply E_WHILE_TRUE. reflexivity.
      - eapply E_SEQ.
        + apply E_ASS. (* Y = 6 *)
        + apply E_ASS. (* X = 1 *)
      - eapply E_WHILE_TRUE. reflexivity.
        + eapply E_SEQ.
          * apply E_ASS. (* Y = 12 *)
          * apply E_ASS. (* X = 0 *)
        + eapply E_WHILE_FALSE. reflexivity.
    Qed.
  End Teorema_2.
End Teoremi.

Close Scope Z.


