Require Import Unicode.Utf8.
Require Import String.

Inductive Loc: Type := string.

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
