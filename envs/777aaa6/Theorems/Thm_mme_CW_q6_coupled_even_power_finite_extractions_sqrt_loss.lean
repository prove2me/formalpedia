-- Prove2me | Theorems.Thm_mme_CW_q6_coupled_even_power_finite_extractions_sqrt_loss
-- name    : mme_CW_q6_coupled_even_power_finite_extractions_sqrt_loss
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T06:13:15.46885+00:00
-- url     : https://prove2.me/theorems/e3445050-e020-41bb-b503-ca39052eb89a
-- title:
--   Coupled q=6 tensor: finite even-power extraction with square-root loss
-- statement:
--   For any field $K$ and real $\tau$ with $3\tau\ge2$, there is $C\ge0$ such that for every sufficiently large integer $N$, the actual tensor $(\operatorname{cyc}(C_6))^{\otimes 2N}$ restricts to a finite direct sum of matrix-multiplication tensors $\langle a_i,b_i,c_i\rangle$ satisfying $$\bigl(4\,6^{3\tau}(6^{3\tau}+2)\bigr)^{2N}\exp(-C\sqrt{N+1})\le\sum_i(a_i b_i c_i)^\tau.$$ The statement retains the subexponential finite loss explicitly and requires no common-halving assumption on the primary family.
-- source:
--   Quantitative consequence of the bounded primary-hash square-root capacity theorem, the primary-family C-tensor certificate, and direct cyclic Behrend extraction.

import Theorems.Thm_mme_CW_q6_primary_hash_family_Ctensor_certificates
import Theorems.Thm_mme_CW_q6_primary_hash_sqrt_capacity_bounded
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
import Theorems.Thm_mme_cyclicSymmetrization_kronPow_isomorphic
import Mathlib.Tactic

open MME BigOperators Filter
universe u
set_option autoImplicit false

theorem mme_CW_q6_coupled_even_power_finite_extractions_sqrt_loss
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
            ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
          (4 * (6 : ℝ) ^ (3 * tau) * ((6 : ℝ) ^ (3 * tau) + 2)) ^ (2 * N) *
              Real.exp (-C * Real.sqrt (((N + 1 : ℕ) : ℝ))) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by sorry
