-- Prove2me | Theorems.Thm_mme_dwz_table2_each_component_six_symmetric_finite_extraction_sqrt_loss
-- name    : mme_dwz_table2_each_component_six_symmetric_finite_extraction_sqrt_loss
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T18:38:26.845709+00:00
-- url     : https://prove2.me/theorems/b918e5dc-8f31-4099-9cfb-90412b76967d
-- title:
--   Table 2: uniform finite extraction for each restricted component
-- statement:
--   Fix $\tau\ge 2/3$. There is one constant $C\ge0$ such that, for all sufficiently large Table-2 scales $m$ and every one of the fifteen restricted component rows $s$, the six-symmetrization of that component power restricts to a finite direct sum of matrix-multiplication tensors whose total $\tau$-weight is at least
--
--   $$
--   B_s(\tau)^{6n_s(m)}\exp\!\left(-C\sqrt{10^{16}m+1}\right).
--   $$
--
--   The uniform statement packages only the rowwise finite extractions: the scalar and rectangular rows, the finite $022/202$ projectors, the exact $220$ row, the enhanced $112$ router, and the distinct cyclic $121/211$ routers. Multiplication of the fifteen rowwise witnesses into the standard tensor is a separate generic step.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Lemma 4.6, the restricted splitting in Section 5, and the component values used in Equation (25) and Table 2, arXiv:2210.10173v5.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Definitions.Def_mme_dwz_square_data
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_six_symmetrized_tau_value

open MME BigOperators Filter
open MME.DWZSquare MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_table2_each_component_six_symmetric_finite_extraction_sqrt_loss
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15,
          ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd
                (fun j => MMObj K (A j) (B j) (Cdim j)))
              (sixSymmetrization (restrictedComponentPower K s m)) ∧
            (((componentBase tau s) ^
                (MME.DWZTable2Counts.component s * m)) ^ (6 : ℕ)) *
                Real.exp
                  (-C * Real.sqrt
                    (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by
  sorry
