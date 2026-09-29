-- Prove2me | Theorems.Thm_mme_dwz_square_equation25_cofinal_finite_extraction
-- name    : mme_dwz_square_equation25_cofinal_finite_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T14:39:49.676538+00:00
-- url     : https://prove2.me/theorems/fab986bf-1f7e-478c-be25-338871a192d8
-- title:
--   Equation (25): cofinal finite direct-sum extraction
-- statement:
--   Fix a field $K$, a parameter $\tau$ satisfying $2\le 3\tau$, and a nonnegative target $V$ strictly below the specialized Table-2 rate $R_{\mathrm{sq}}(\tau)$. There are a cofinal sequence of tensor powers $s(n)$ and a real loss $\delta_n\to0$ such that, for all sufficiently large $n$, the $s(n)$-th power of the full six-symmetrization of the literal tensor square $CW_6\otimes CW_6$ restricts to a finite direct sum of matrix-multiplication tensors and
--
--   $$
--   (V^6)^{s(n)}(1-\delta_n)\le\sum_i(a_i b_i c_i)^\tau.
--   $$
--
--   This is the finite, witnessed extraction underlying the strict-below form of Duan--Wu--Zhou Equation (25). It retains the actual restriction maps and the complete direct sum, while isolating the cofinality and subexponential-loss bookkeeping from the abstract definition of six-symmetrized tau-value.
--
--   **Formalization Note** The sixth power is the normalization built into `HasSixSymmetricTauValueAtLeast`. The imported source-mask, 112-profile, retained-rate, and Hole-repair results are the completed interfaces used to construct the finite witnesses; the remaining work is their global source-faithful assembly.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173, Equation (25), Algorithm 2, and Section 6.3 (printed pp. 57-59 / PDF pp. 58-60), https://arxiv.org/abs/2210.10173

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_dwz_flat_seven_eighths_restrict_standard
import Theorems.Thm_mme_dwz_square_rate_power_eq_retained_mul_component_product
import Theorems.Thm_mme_dwz_q6_112_exact_address_allowed_histogram
import Theorems.Thm_mme_dwz_source_aligned_address_word_survives_iff_exists_nonhole
import Theorems.Thm_mme_dwz_source_aligned_broken_address_projection_certificate
import Theorems.Thm_mme_tensor_family_direct_sum_restrict_of_mixed_maps
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Theorems.Thm_mme_dwz_table2_broken_copy_transport_to_standard
import Theorems.Thm_mme_dwz_source_broken_family_restrict_grouped_standard

open MME BigOperators Filter
open MME.DWZSquare

universe u

set_option autoImplicit false

theorem mme_dwz_square_equation25_cofinal_finite_extraction
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V) (hVlt : V < squareRate tau) :
    ∃ (s : ℕ → ℕ) (loss : ℕ → ℝ),
      Tendsto s atTop atTop ∧
      Tendsto loss atTop (nhds 0) ∧
      ∀ᶠ n : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((sixSymmetrization
              (TensorObj.kron (CWObj K 6) (CWObj K 6))).kronPow (s n)) ∧
          (V ^ (6 : ℕ)) ^ (s n) * (1 - loss n) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  sorry
