-- Prove2me | Theorems.Thm_OrderlyFriedman_single_leaf
-- name    : OrderlyFriedman.single_leaf
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:45:49.896775+00:00
-- url     : https://prove2.me/theorems/468129eb-beb4-4dce-aac6-ba462f2e2be5
-- title:
--   An expression with a single digit literal evaluates to plus or minus that
-- statement:
--   An expression with a single digit literal evaluates to plus or minus that
--   digit.
--
--   ```lean
--   theorem OrderlyFriedman.single_leaf(e : FExpr) (h1 : numLits e = 1) :
--       ∃ d : Nat, digitSeq e = [d] ∧ (eval e = (d : Int) ∨ eval e = -(d : Int)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/OrderlyFriedman.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/OrderlyFriedman.lean#L134

-- Thm stub generated from Probability/OrderlyFriedman.lean
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

theorem OrderlyFriedman.single_leaf(e : FExpr) (h1 : numLits e = 1) :
    ∃ d : Nat, digitSeq e = [d] ∧ (eval e = (d : Int) ∨ eval e = -(d : Int)) := by sorry
