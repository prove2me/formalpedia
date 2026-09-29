-- Prove2me | Definitions.Def_Probability_OrderlyFriedman
-- name    : Probability_OrderlyFriedman
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:25:26.595358+00:00
-- url     : https://prove2.me/theorems/bce63aac-367f-41f9-b2ce-dbd432e5f691
-- title:
--   Aether Catalog definitions — Probability_OrderlyFriedman
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.OrderlyFriedman`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/OrderlyFriedman.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Orderly Friedman numbers (OEIS A080035)

A *Friedman number* is a positive integer that can be written, in a nontrivial
way, as an expression using its own digits (each digit used exactly once, in any
order) together with the operations `+`, `*`, exponentiation, unary minus and
parentheses.  An *orderly* Friedman number (OEIS A080035) is a Friedman number
admitting such an expression in which the digits appear in their natural reading
order (most-significant first).

This file formalizes orderly Friedman numbers.  We model digit expressions by an
inductive type `FExpr` over a small set of binary operations `FOp`
(`add`, `mul`, `pow`), with unary negation and single-digit literals.  We define
`eval` (the integer value of an expression), `digitSeq` (the left-to-right
sequence of digit literals) and `numLits` (the number of digit literals).

The predicate `IsOrderlyFriedman n` asks for an expression with at least two
digit literals whose digit sequence equals the digits of `n` in reading order
(`(Nat.digits 10 n).reverse`) and which evaluates to `n`.  The predicate
`IsFriedman n` only requires the digit sequence to be a permutation of the digits
of `n`.

Main results:
* five explicit witnesses (`127`, `343`, `736`, `1285`, `2592`);
* `numLits_eq_length`: `numLits e = (digitSeq e).length`;
* `orderlyFriedman_ge_ten`: orderly Friedman numbers have at least two digits;
* `no_two_digit_orderlyFriedman`: there are no two-digit orderly Friedman numbers;
* `orderly_imp_friedman`: every orderly Friedman number is a Friedman number;
* `digits_in_order`: the defining expression has its digits in reading order.
-/

namespace OrderlyFriedman

/-- The binary operations allowed in digit expressions. -/
inductive FOp
  | add
  | mul
  | pow
  deriving DecidableEq, Repr

/-- Digit expressions: single-digit literals, unary negation and binary
operations. -/
inductive FExpr
  | lit (d : Nat)
  | neg (e : FExpr)
  | bin (op : FOp) (l r : FExpr)
  deriving Repr

/-- Apply a binary operation to two integers.  Exponentiation uses the
natural-number truncation of the exponent. -/
def FOp.apply : FOp → Int → Int → Int
  | FOp.add, a, b => a + b
  | FOp.mul, a, b => a * b
  | FOp.pow, a, b => a ^ b.toNat

/-- The integer value of a digit expression. -/
def eval : FExpr → Int
  | FExpr.lit d => (d : Int)
  | FExpr.neg e => - eval e
  | FExpr.bin op l r => op.apply (eval l) (eval r)

/-- The left-to-right sequence of digit literals occurring in an expression. -/
def digitSeq : FExpr → List Nat
  | FExpr.lit d => [d]
  | FExpr.neg e => digitSeq e
  | FExpr.bin _ l r => digitSeq l ++ digitSeq r

/-- The number of digit literals in an expression. -/
def numLits : FExpr → Nat
  | FExpr.lit _ => 1
  | FExpr.neg e => numLits e
  | FExpr.bin _ l r => numLits l + numLits r

/-- `n` is an *orderly Friedman number*: it can be written using its own digits,
in reading order, with at least two digit literals. -/
def IsOrderlyFriedman (n : Nat) : Prop :=
  ∃ e : FExpr, numLits e ≥ 2 ∧ digitSeq e = (Nat.digits 10 n).reverse ∧ eval e = (n : Int)

/-- `n` is a *Friedman number*: it can be written using its own digits, in any
order, with at least two digit literals. -/
def IsFriedman (n : Nat) : Prop :=
  ∃ e : FExpr, numLits e ≥ 2 ∧ (digitSeq e).Perm (Nat.digits 10 n) ∧ eval e = (n : Int)

/-! ## Explicit witnesses -/






/-! ## Structural lemmas -/




/-- A value `v` is *reachable* from two digits `a`, `b` (in this order) if it can
be obtained by combining `±a` and `±b` with one operation and an outer sign. -/
def reachable2 (a b : Nat) (v : Int) : Prop :=
  ∃ s0 s1 s2 : Bool,
      v = (if s0 then -1 else 1) *
            ((if s1 then -(a : Int) else (a : Int)) + (if s2 then -(b : Int) else (b : Int)))
    ∨ v = (if s0 then -1 else 1) *
            ((if s1 then -(a : Int) else (a : Int)) * (if s2 then -(b : Int) else (b : Int)))
    ∨ v = (if s0 then -1 else 1) *
            ((if s1 then -(a : Int) else (a : Int)) ^ (if s2 then -(b : Int) else (b : Int)).toNat)

instance (a b : Nat) (v : Int) : Decidable (reachable2 a b v) := by
  unfold reachable2
  infer_instance









end OrderlyFriedman


