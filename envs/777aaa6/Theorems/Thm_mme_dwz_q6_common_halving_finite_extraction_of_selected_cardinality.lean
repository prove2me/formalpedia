-- Prove2me | Theorems.Thm_mme_dwz_q6_common_halving_finite_extraction_of_selected_cardinality
-- name    : mme_dwz_q6_common_halving_finite_extraction_of_selected_cardinality
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T01:58:14.684383+00:00
-- url     : https://prove2.me/theorems/61183e31-d41b-48d8-be9c-e6d6a9f50483
-- title:
--   A selected-cardinality budget implies common-halving finite extraction
-- statement:
--   Let $K$ be a field, $\tau\in\mathbb R$, $s\in\{13,14\}$, and $N=c_s m$. Suppose a primary $q=6$ family with $A$ fibers and $H$ entries per fiber has a common balanced halving and a paired-induced selection of $q$ entries. Assume
--   $$A^3H^2\exp(-200\sqrt{N+1})\leq q^3.$$
--   Writing $R_{s,m}$ for the allowed-word restricted component power, there is a matrix direct sum satisfying
--   $$\bigoplus_j\langle a_j,b_j,c_j\rangle\leq\operatorname{sixSym}(R_{s,m}),\qquad A^3H^2\left((6^{4G+2L})^3\right)^\tau\exp(-200\sqrt{N+1})\leq\sum_j(a_jb_jc_j)^\tau.$$
--   This gives the prescribed finite-extraction conclusion whenever a sufficiently large paired-induced selection is available. Existence of such a selection is an additional hypothesis, not a conclusion.
-- source:
--   Selected component projections, disallowed-word descent, component matrix certificates, and cyclic expansion of equal-volume matrix sums.

import Definitions.Def_mme_dwz_component_pair_projection_data
import Definitions.Def_mme_CW_q6_paired_cyclic_induced
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
open MME MME.DWZComponentRestriction BigOperators
universe u
set_option autoImplicit false

theorem mme_dwz_q6_common_halving_finite_extraction_of_selected_cardinality
    {K : Type u} [Field K] (tau : ℝ)
    (s : Fin 15) (hs : s = 13 ∨ s = 14) (m L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily (DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving)
    (q : ℕ) (index : Fin q → Fin A × Fin H)
    (hselected : ∀ p0 p1 p2, family.PairedCyclicSupported halving
      (index p0) (index p1) (index p2) → p0 = p1 ∧ p1 = p2)
    (hsize : (A : ℝ) ^ 3 * (H : ℝ) ^ 2 * Real.exp (-200 * Real.sqrt
      (((DWZTable2Counts.component s * m + 1 : ℕ) : ℝ))) ≤ (q : ℝ) ^ 3) :
    ∃ (Q : ℕ) (a b c : Fin Q → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (restrictedComponentPower K s m)) ∧
      (((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2) *
          ((((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ) : ℝ) ^ tau) *
          Real.exp (-200 * Real.sqrt
            (((DWZTable2Counts.component s * m + 1 : ℕ) : ℝ))) ≤
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by sorry
