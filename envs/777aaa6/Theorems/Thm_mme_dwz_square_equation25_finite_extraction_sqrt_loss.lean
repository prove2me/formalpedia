-- Prove2me | Theorems.Thm_mme_dwz_square_equation25_finite_extraction_sqrt_loss
-- name    : mme_dwz_square_equation25_finite_extraction_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T17:19:36.968591+00:00
-- url     : https://prove2.me/theorems/693f9742-ea29-4537-9d1a-26204c1f0b07
-- title:
--   Equation (25): finite extraction with explicit square-root-exponential loss
-- statement:
--   Fix a field $K$ and a real parameter $\tau$ satisfying $2\le3\tau$. Let $M=10^{16}$ be the common denominator of the exact Table-2 data. There is a constant $C\ge0$ such that, for every sufficiently large natural number $m$, the $(Mm)$-th power of the full six-symmetrization of the literal square $CW_6\otimes CW_6$ restricts to a finite direct sum of matrix-multiplication tensors and
--
--   $$
--   \bigl(R_{\mathrm{sq}}(\tau)^6\bigr)^{Mm}
--   \exp\bigl(-C\sqrt{Mm+1}\bigr)
--   \le\sum_i(a_i b_i c_i)^\tau.
--   $$
--
--   This is the finite tensor-extraction core of the specialized Duan--Wu--Zhou Equation (25). The single square-root-exponential term absorbs the polynomial type-count losses, the Salem--Spencer density loss, the first and second asymmetric-hash pruning losses, and the fixed-size Hole-repair amplification. The statement retains a witnessed restriction from the actual six-symmetrized CW square; it does not replace the surviving tensors by a scalar counting certificate.
--
--   The theorem is deliberately stronger than a strict-subendpoint asymptotic statement. A separate proved absorption lemma shows that every $V<R_{\mathrm{sq}}(\tau)$ eventually dominates this loss, yielding the cofinal tau-value witness.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023, arXiv:2210.10173, Lemma 3.3, Lemma 5.6, Corollary 5.11, Lemma 6.7, Claim 6.8, Equation (25), and Section 6.3/Table 2 (printed pp. 18, 48-50, and 57-59 / PDF pp. 19, 49-51, and 58-60), https://arxiv.org/abs/2210.10173

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_CW_tensor
import Definitions.Def_mme_six_symmetrized_tau_value
import Theorems.Thm_mme_dwz_flat_seven_eighths_restrict_standard
import Theorems.Thm_mme_dwz_square_rate_power_eq_retained_mul_component_product
import Theorems.Thm_mme_dwz_q6_112_exact_address_allowed_histogram
import Theorems.Thm_mme_dwz_table2_broken_copy_transport_to_standard
import Theorems.Thm_mme_dwz_source_broken_family_restrict_grouped_standard

open MME BigOperators Filter
open MME.DWZSquare

universe u

set_option autoImplicit false

theorem mme_dwz_square_equation25_finite_extraction_sqrt_loss
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ (k : ℕ) (a b c : Fin k → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
            ((sixSymmetrization
              (TensorObj.kron (CWObj K 6) (CWObj K 6))).kronPow
                (MME.DWZTable2Counts.scale * m)) ∧
          ((squareRate tau) ^ (6 : ℕ)) ^
                (MME.DWZTable2Counts.scale * m) *
              Real.exp
                (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
            ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  sorry
