-- Prove2me | solution 1 for OrderlyFriedman.single_leaf
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:49:31.822347+00:00
-- url     : https://prove2.me/submissions/ea1cce81-585d-48fe-af38-8b7fef1eb9d1

-- Sol generated from Probability/OrderlyFriedman.lean
import Mathlib
import Definitions.Def_Probability_OrderlyFriedman
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

open OrderlyFriedman









/-! ## Explicit witnesses -/






/-! ## Structural lemmas -/


/-- Every expression has at least one digit literal. -/
theorem numLits_pos (e : FExpr) : 1 ≤ numLits e := by
  induction e with
  | lit d => simp [numLits]
  | neg e ih => simpa [numLits] using ih
  | bin op l r ihl ihr => simp [numLits]; omega













open OrderlyFriedman in
theorem solution(e : FExpr) (h1 : numLits e = 1) :
    ∃ d : Nat, digitSeq e = [d] ∧ (eval e = (d : Int) ∨ eval e = -(d : Int)) := by
  induction e with
  | lit d => exact ⟨d, rfl, Or.inl rfl⟩
  | neg e ih =>
      obtain ⟨d, hd, hv⟩ := ih (by simpa [numLits] using h1)
      refine ⟨d, by simpa [digitSeq] using hd, ?_⟩
      rcases hv with hv | hv
      · exact Or.inr (by simp [eval, hv])
      · exact Or.inl (by simp [eval, hv])
  | bin op l r ihl ihr =>
      exfalso
      have hl := numLits_pos l
      have hr := numLits_pos r
      simp [numLits] at h1
      omega
