From Coq Require Import Init.Nat.
From Coq Require Import Strings.String.
From Coq Require Import Lists.List.

Inductive type : Type :=
  | int
  | array (_ : type)
  | immut (_ : type)
  | monitor (_ : string)
  | unlocked (_ : string)
  .

Inductive exp : Type :=
  | number (n : nat)
  | lhs (s : string)
  | call_exp : call -> exp
  | typecast : exp -> type -> exp
  | monitor_constructor (s : string)
  | array_constructor (_ : type)
  | array_literal (_ : list exp)
  | immut_array_literal (_ : list exp)

with call : Type :=
  | function_call : string -> exp -> call
  | method_call : exp -> string -> exp -> call
  .

Inductive variable_def : Type :=
  | val : string -> exp -> variable_def
  | var_dec : string -> type -> variable_def
  | var_def : string -> exp -> variable_def
  .

Inductive statement : Type :=
  | call_stat (_ : call)
  | assignment : string -> exp -> statement
  | ret (_ : exp)
  | wait : exp -> exp -> statement
  | signal : exp -> statement
  | broadcast : exp -> statement
  | spawn : block -> statement
  | acquireval : string -> type -> exp -> block -> statement

with block : Type :=
  | v (_ : variable_def)
  | s (_ : statement)
  | b (_ : list block)
  .

Inductive function_def : Type :=
  | function : string -> (string -> type) -> block -> function_def
  .

Inductive method_def : Type :=
  | private (_ : function_def)
  | acquire (_ : function_def)
  | release (_ : function_def)
  .

Inductive monitor_block : Type :=
  | mv (_ : variable_def)
  | mm (_ : method_def)
  .

Inductive monitor_def : Type :=
  | mon : string -> monitor_block -> monitor_def
  .

Inductive global_def : Type :=
  | global_variable (def : variable_def)
  | global_function (def : function_def)
  | global_monitor (def : monitor_def)
  .

Inductive program : Type := code (_ : list global_def).
