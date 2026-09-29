-- Prove2me | solution 1 for OrderlyFriedman.reachable2_of
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:49:31.303309+00:00
-- url     : https://prove2.me/submissions/a3c37093-5e77-4958-8915-ed56bb7eeed8

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















open OrderlyFriedman in
theorem solution(a b : Nat) (x y : Int) (op : FOp)
    (hx : x = (a : Int) ∨ x = -(a : Int)) (hy : y = (b : Int) ∨ y = -(b : Int)) :
    reachable2 a b (op.apply x y) := by
  obtain ⟨s1, hx⟩ : ∃ s1 : Bool, x = if s1 then -(a : Int) else (a : Int) := by
    rcases hx with h | h
    · exact ⟨false, by simp [h]⟩
    · exact ⟨true, by simp [h]⟩
  obtain ⟨s2, hy⟩ : ∃ s2 : Bool, y = if s2 then -(b : Int) else (b : Int) := by
    rcases hy with h | h
    · exact ⟨false, by simp [h]⟩
    · exact ⟨true, by simp [h]⟩
  refine ⟨false, s1, s2, ?_⟩
  subst hx; subst hy
  cases op
  · exact Or.inl (by simp [FOp.apply])
  · exact Or.inr (Or.inl (by simp [FOp.apply]))
  · exact Or.inr (Or.inr (by simp [FOp.apply]))
