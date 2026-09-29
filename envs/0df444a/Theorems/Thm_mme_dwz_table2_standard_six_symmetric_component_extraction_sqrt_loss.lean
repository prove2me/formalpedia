-- Prove2me | Theorems.Thm_mme_dwz_table2_standard_six_symmetric_component_extraction_sqrt_loss
-- name    : mme_dwz_table2_standard_six_symmetric_component_extraction_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T17:56:19.199682+00:00
-- url     : https://prove2.me/theorems/e2ba3f8b-636d-4572-995e-2a8a1a3cd7d4
-- title:
--   Table 2: six-symmetric finite extraction of all fifteen restricted components
-- statement:
--   Fix $\tau\ge2/3$. For each positive Table-2 scale $m$, let $T^*_{m}$ be the literal standard tensor obtained as the ordered Kronecker product of the fifteen prescribed restricted component powers. There is a constant $C\ge0$ such that, for all sufficiently large $m$, the full six-symmetrization of $T^*_{m}$ restricts to a finite direct sum of matrix-multiplication tensors satisfying
--
--   $$
--   \left(\prod_{s=1}^{15}B_s(\tau)^{n_s(m)}\right)^6
--    e^{-C\sqrt{10^{16}m+1}}
--   \le\sum_j(A_jB_jC_j)^\tau.
--   $$
--
--   This is the component-only half of the finite Equation-(25) extraction. It is designed to reuse the existing Coppersmith--Winograd square component machinery: the scalar and rectangular rows, the exact 220 row, the finite 022/202 projectors, the enhanced 112 extraction, and its distinct cyclic 121/211 routers. It contains no asymmetric outer hashing or Hole-Lemma counting.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, FOCS 2023 / arXiv:2210.10173, the restricted-splitting component values in Lemma 4.6, their cyclic six-symmetric assembly, Equation (25), and Section 6.3/Table 2, printed pp. 31-32 and 58-59.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_table2_standard_obj
import Definitions.Def_mme_six_symmetrized_tau_value

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_table2_standard_six_symmetric_component_extraction_sqrt_loss
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
          TensorObj.Restrict
            (TensorObj.bigAdd
              (fun j => MMObj K (A j) (B j) (Cdim j)))
            (sixSymmetrization (dwzTable2StandardObj K m)) ∧
          ((∏ s : Fin 15,
              (componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
              Real.exp
                (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
            ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  sorry
