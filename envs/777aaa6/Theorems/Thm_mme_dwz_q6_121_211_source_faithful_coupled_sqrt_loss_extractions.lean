-- Prove2me | Theorems.Thm_mme_dwz_q6_121_211_source_faithful_coupled_sqrt_loss_extractions
-- name    : mme_dwz_q6_121_211_source_faithful_coupled_sqrt_loss_extractions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:18:21.149174+00:00
-- url     : https://prove2.me/theorems/42f80eed-fb0c-44ec-afdf-5559fcc704eb
-- title:
--   DWZ Table 2 rows 121/211: source-faithful coupled extraction with square-root loss
-- statement:
--   Fix a field $K$ and $\tau\ge2/3$. For each of the two rotated coupled constituents $121$ and $211$ in Duan--Wu--Zhou Table 2, take the literal canonical component power with its prescribed equal two-way fine-word split and apply full six-symmetrization. There is a constant $C\ge0$ such that, for every sufficiently large Table-2 multiplier $m$, this source tensor restricts to a finite direct sum of matrix-multiplication tensors with
--
--   $$
--   \left(4\,6^{3\tau}(6^{3\tau}+2)\right)^{2N_s(m)}\exp\left(-C\sqrt{10^{16}m+1}\right)\le\sum_j(A_jB_jC_j)^{\tau}.
--   $$
--
--   Here $N_s(m)$ is the exact integer count of row $s$ multiplied by $m$. The statement retains the actual allowed-word projection rather than replacing it with the unrestricted coupled tensor. It isolates the source-labelled cyclic routing and primary asymmetric-hash extraction from the elementary cube identity for the displayed Table-2 component base.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Definition 3.3, the 121/211 value in Section 6.3, Equation (25), and Table 2 (printed pp. 18 and 58-59); https://arxiv.org/abs/2210.10173

import Mathlib.Analysis.SpecificLimits.Basic
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_dwz_table2_integer_counts
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_six_symmetrized_tau_value

open MME BigOperators Filter
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_121_211_source_faithful_coupled_sqrt_loss_extractions
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        ∀ s : Fin 15, (s = 13 ∨ s = 14) →
          ∃ (q : ℕ) (A B Cdim : Fin q → ℕ),
            TensorObj.Restrict
              (TensorObj.bigAdd
                (fun j ↦ MMObj K (A j) (B j) (Cdim j)))
              (sixSymmetrization (restrictedComponentPower K s m)) ∧
            (4 * (6 : ℝ) ^ (3 * tau) *
                ((6 : ℝ) ^ (3 * tau) + 2)) ^
                  (2 * (MME.DWZTable2Counts.component s * m)) *
                Real.exp (-C * Real.sqrt
                  (((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ))) ≤
              ∑ j, (((A j * B j * Cdim j : ℕ) : ℝ) ^ tau) := by sorry
