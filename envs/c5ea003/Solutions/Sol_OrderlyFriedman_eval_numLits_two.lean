-- Prove2me | solution 1 for OrderlyFriedman.eval_numLits_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:52:36.840932+00:00
-- url     : https://prove2.me/submissions/38cc0d96-65ac-40a3-b66c-3899cf1383db

-- Sol generated from Probability/OrderlyFriedman.lean
import Mathlib
import Definitions.Def_Probability_OrderlyFriedman
import Theorems.Thm_OrderlyFriedman_reachable2_of
import Theorems.Thm_OrderlyFriedman_single_leaf
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





/-- Reachable values are closed under negation. -/
theorem reachable2_neg (a b : Nat) (v : Int) (h : reachable2 a b v) :
    reachable2 a b (-v) := by
  obtain ⟨s0, s1, s2, h⟩ := h
  refine ⟨!s0, s1, s2, ?_⟩
  have hsgn : (if !s0 then (-1 : Int) else 1) = -(if s0 then (-1 : Int) else 1) := by
    cases s0 <;> rfl
  rcases h with h | h | h
  · exact Or.inl (by rw [h, hsgn]; ring)
  · exact Or.inr (Or.inl (by rw [h, hsgn]; ring))
  · exact Or.inr (Or.inr (by rw [h, hsgn]; ring))








open OrderlyFriedman in
theorem solution(e : FExpr) (a b : Nat) (h2 : numLits e = 2)
    (hd : digitSeq e = [a, b]) : reachable2 a b (eval e) := by
  induction e with
  | lit d => simp [numLits] at h2
  | neg e ih =>
      have h2' : numLits e = 2 := by simpa [numLits] using h2
      have hd' : digitSeq e = [a, b] := by simpa [digitSeq] using hd
      have hrec := ih h2' hd'
      have hev : eval (FExpr.neg e) = - eval e := rfl
      rw [hev]
      exact reachable2_neg a b (eval e) hrec
  | bin op l r ihl ihr =>
      -- both sides are single leaves
      have hl1 : numLits l = 1 := by
        have := numLits_pos l; have := numLits_pos r
        simp [numLits] at h2; omega
      have hr1 : numLits r = 1 := by
        have := numLits_pos l; have := numLits_pos r
        simp [numLits] at h2; omega
      obtain ⟨da, hda, hva⟩ := single_leaf l hl1
      obtain ⟨db, hdb, hvb⟩ := single_leaf r hr1
      have hsplit : [da, db] = [a, b] := by
        have : digitSeq (FExpr.bin op l r) = [da, db] := by simp [digitSeq, hda, hdb]
        rw [this] at hd; exact hd
      have hda' : da = a := by simpa using congrArg (·.headI) hsplit
      have hdb' : db = b := by
        have := congrArg (·.tail) hsplit
        simpa using this
      have hev : eval (FExpr.bin op l r) = op.apply (eval l) (eval r) := rfl
      rw [hev, ← hda', ← hdb']
      exact reachable2_of da db (eval l) (eval r) op hva hvb
