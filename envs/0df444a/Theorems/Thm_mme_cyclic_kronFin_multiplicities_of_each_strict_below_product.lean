-- Prove2me | Theorems.Thm_mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
-- name    : mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:17:31.209392+00:00
-- url     : https://prove2.me/theorems/7d3ff53a-6ec0-47c6-aeb3-e6f2f2f07317
-- title:
--   Strict local cyclic tensor values multiply with arbitrary multiplicities
-- statement:
--   Let $T_i$ be a finite family of order-three tensors, let $d_i$ be natural multiplicities, and let $e_i>0$. Suppose the cyclic symmetrization of each $T_i$ has $\tau$-value at least every nonnegative value strictly below $e_i$. Then the cyclic symmetrization of the product $\bigboxtimes_i T_i^{\boxtimes d_i}$ has $\tau$-value at least every nonnegative $W$ strictly below $\prod_i e_i^{d_i}$. This packages all finite synchronization and approximation losses into one reusable product theorem.
-- source:
--   Coppersmith--Winograd laser-method value multiplicativity; finite strict-endpoint form used in A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Lemma 5.1, pp. 356--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Mathlib.Tactic
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_tau_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_cyclic_kronFin_multiplicities_of_each_strict_below_product
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (multiplicity : Fin n → ℕ)
    (tau : ℝ) (endpoint : Fin n → ℝ)
    (hendpoint : ∀ i, 0 < endpoint i)
    (hlocal : ∀ (i : Fin n) (V : ℝ),
      0 ≤ V → V < endpoint i →
      HasTauValueAtLeast (cyclicSymmetrization (T i)) tau V) :
    ∀ W : ℝ, 0 ≤ W →
      W < ∏ i, (endpoint i) ^ (multiplicity i) →
      HasTauValueAtLeast
        (cyclicSymmetrization
          (TensorObj.kronFin n
            (fun i ↦ (T i).kronPow (multiplicity i)))) tau W := by
  sorry
