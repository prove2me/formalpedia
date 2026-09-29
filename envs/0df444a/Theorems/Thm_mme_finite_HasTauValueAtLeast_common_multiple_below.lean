-- Prove2me | Theorems.Thm_mme_finite_HasTauValueAtLeast_common_multiple_below
-- name    : mme_finite_HasTauValueAtLeast_common_multiple_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:59:23.295127+00:00
-- url     : https://prove2.me/theorems/0fd04c9f-ddc1-49c2-a504-e454ae8e7a9d
-- title:
--   Synchronize finitely many strict tau-values on one power lattice
-- statement:
--   For a finite family of tensors, suppose the `i`-th tensor has tau-value at least a positive base `B_i`, and choose a nonnegative strict target `V_i<B_i`. Then there is one positive integer `E` such that, for every nonnegative integer `r`, every component simultaneously has a genuine finite MM extraction from its `rE`-th tensor power with total tau-weight at least `V_i^(rE)`. This provides an explicit common cofinal integral exponent lattice.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definition 3.4 and the synchronized component product in Section 6.3 and Equation (25), PDF pp. 13 and 59-60; https://arxiv.org/abs/2210.10173. The theorem makes the finite common-divisibility argument explicit rather than assuming intersections of frequent exponent sets.

import Mathlib.Tactic
import Theorems.Thm_mme_HasTauValueAtLeast_multiple_extractions_below

open BigOperators
open MME

set_option autoImplicit false

universe u

theorem mme_finite_HasTauValueAtLeast_common_multiple_below
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (tau : ℝ)
    (base target : Fin n → ℝ)
    (hbase : ∀ i, 0 < base i)
    (htarget : ∀ i, 0 ≤ target i)
    (hstrict : ∀ i, target i < base i)
    (hvalue : ∀ i, HasTauValueAtLeast (T i) tau (base i)) :
    ∃ E : ℕ, 0 < E ∧
      ∀ (r : ℕ) (i : Fin n),
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
            ((T i).kronPow (r * E)) ∧
          (target i) ^ (r * E) ≤
            ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by sorry
