-- Prove2me | Theorems.Thm_mme_HasTauValueAtLeast_kronFin_multiplicities_of_each_strict_below_product
-- name    : mme_HasTauValueAtLeast_kronFin_multiplicities_of_each_strict_below_product
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:00:57.997467+00:00
-- url     : https://prove2.me/theorems/f62e7879-88f5-4197-bcdd-1243d224ac7c
-- title:
--   Strict local tau-values multiply with arbitrary finite multiplicities
-- statement:
--   Let $T_0,\ldots,T_{n-1}$ be order-three tensors over a field, let $e_i>0$, and let $d_i$ be nonnegative integer multiplicities. Suppose that, for every $i$, the tensor $T_i$ attains every nonnegative tau-value strictly below $e_i$. Then the weighted Kronecker product $\boxtimes_i T_i^{\boxtimes d_i}$ attains every nonnegative value strictly below $$\prod_{i=0}^{n-1} e_i^{d_i}.$$ The conclusion includes zero multiplicities and is downward-closed at the total endpoint. It is a generic synchronization and finite-product principle, independent of any particular laser profile.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), value multiplicativity and simultaneous tensor-power extraction on journal pp. 264--265; https://www.sciencedirect.com/science/article/pii/S0747717108800132. Formal finite synchronization builds on the platform common-power extraction theorem.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_tau_value

open MME BigOperators

universe u

set_option autoImplicit false

theorem mme_HasTauValueAtLeast_kronFin_multiplicities_of_each_strict_below_product
    {K : Type u} [Field K] {n : ℕ}
    (T : Fin n → TensorObj K 3) (multiplicity : Fin n → ℕ)
    (tau : ℝ) (endpoint : Fin n → ℝ)
    (hendpoint : ∀ i, 0 < endpoint i)
    (hlocal : ∀ (i : Fin n) (V : ℝ),
      0 ≤ V → V < endpoint i →
      HasTauValueAtLeast (T i) tau V) :
    ∀ W : ℝ, 0 ≤ W →
      W < ∏ i, (endpoint i) ^ (multiplicity i) →
      HasTauValueAtLeast
        (TensorObj.kronFin n
          (fun i ↦ (T i).kronPow (multiplicity i))) tau W := by
  sorry
