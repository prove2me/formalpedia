-- Prove2me | solution 1 for OrderlyFriedman.no_two_digit_orderlyFriedman
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:54:02.1362+00:00
-- url     : https://prove2.me/submissions/33aec7bc-b533-4370-bc34-9f568887234a

-- Sol generated from Probability/OrderlyFriedman.lean
import Mathlib
import Definitions.Def_Probability_OrderlyFriedman
import Theorems.Thm_OrderlyFriedman_eval_numLits_two
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

/-- The number of digit literals equals the length of the digit sequence. -/
theorem numLits_eq_length (e : FExpr) : numLits e = (digitSeq e).length := by
  induction e with
  | lit d => rfl
  | neg e ih => simpa [numLits, digitSeq] using ih
  | bin op l r ihl ihr => simp [numLits, digitSeq, ihl, ihr]









/-- For valid two-digit data `a, b` (with `1 ≤ a ≤ 9`, `b ≤ 9`), the number
`10*a + b` is not reachable from `a` and `b`. -/
theorem not_reachable2 (a b : Nat) (ha : 1 ≤ a) (ha9 : a ≤ 9) (hb : b ≤ 9) :
    ¬ reachable2 a b (10 * a + b) := by
  interval_cases a <;> interval_cases b <;> decide





open OrderlyFriedman in
theorem solution{n : Nat} (hlo : 10 ≤ n) (hhi : n < 100) :
    ¬ IsOrderlyFriedman n := by
  rintro ⟨e, hlits, hdig, heval⟩
  -- digits of a two-digit number
  have hdigits : Nat.digits 10 n = [n % 10, n / 10] := by
    have e1 : Nat.digits 10 n = n % 10 :: Nat.digits 10 (n / 10) :=
      Nat.digits_def' (by norm_num) (by omega)
    have e2 : Nat.digits 10 (n / 10) = (n / 10) % 10 :: Nat.digits 10 (n / 10 / 10) :=
      Nat.digits_def' (by norm_num) (by omega)
    have h0 : n / 10 / 10 = 0 := by omega
    have hmod : (n / 10) % 10 = n / 10 := Nat.mod_eq_of_lt (by omega)
    rw [e1, e2, h0, hmod]
    simp
  have hd : digitSeq e = [n / 10, n % 10] := by
    rw [hdig, hdigits]; rfl
  have h2 : numLits e = 2 := by
    rw [numLits_eq_length, hd]; rfl
  have hr : reachable2 (n / 10) (n % 10) (eval e) :=
    eval_numLits_two e (n / 10) (n % 10) h2 hd
  rw [heval] at hr
  have hn : (n : Int) = 10 * (n / 10 : Nat) + (n % 10 : Nat) := by
    have := Nat.div_add_mod n 10
    push_cast
    omega
  rw [hn] at hr
  exact not_reachable2 (n / 10) (n % 10) (by omega) (by omega) (by omega) hr
