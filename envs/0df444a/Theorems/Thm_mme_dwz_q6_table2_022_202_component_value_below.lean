-- Prove2me | Theorems.Thm_mme_dwz_q6_table2_022_202_component_value_below
-- name    : mme_dwz_q6_table2_022_202_component_value_below
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-26T06:20:55.530689+00:00
-- url     : https://prove2.me/theorems/84b46f7d-996d-45e1-acbd-bd3a98512081
-- title:
--   Strict-below tau-value of the canonical Table-2 022 and 202 blocks
-- statement:
--   Let $K$ be a field and let $\tau$ satisfy $2\leq 3\tau$. Denote by $B_\tau$ the common DWZ Table-2 component base for the canonical $022$ and $202$ constituents (indices $9$ and $10$). For every real $V$ with $0\leq V<B_\tau$, prove that both canonical block subtensors have asymptotic $\tau$-value at least $V$:
--
--   $$
--   V_\tau(T_{022})\geq V
--   \qquad\text{and}\qquad
--   V_\tau(T_{202})\geq V.
--   $$
--
--   The value assertion is witnessed by actual matrix-multiplication restrictions along the cofinal divisible sequence $m=10^8t$. Thus it realizes the normalized Table-2 scalar formula as a genuine strict-below tensor-value statement for both orientations.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 / FOCS 2023, Section 6.3 and Table 2, especially the 022/202 component-value entry; https://arxiv.org/abs/2210.10173. The strict-below formulation is the witness-level asymptotic realization of that component value.

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Theorems.Thm_mme_dwz_q6_table2_022_202_prescribed_dimension_restriction
import Theorems.Thm_mme_dwz_q6_table2_022_polynomial_loss_le_exp_sqrt
import Theorems.Thm_mme_dwz_q6_table2_022_component_power_le_dimension
import Theorems.Thm_mme_strict_pow_absorbs_sqrt_exp_loss
import Theorems.Thm_mme_HasTauValueAtLeast_of_cofinal_finite_extractions

open Filter Topology
open MME BigOperators MME.DWZSquare MME.DWZTable2Component022

universe u

set_option autoImplicit false

theorem mme_dwz_q6_table2_022_202_component_value_below
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt : V < componentBase tau (9 : Fin 15)) :
    HasTauValueAtLeast
        ((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType 0 2 2)) tau V ∧
      HasTauValueAtLeast
        ((cwSquareCanonicalGrading K 6).blockSubtensor
          (cwSquareBlockType 2 0 2)) tau V := by
  sorry
