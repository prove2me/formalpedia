-- Prove2me | solution 1 for mme_dwz_q6_common_halving_finite_extraction_of_selected_cardinality
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T01:58:26.233836+00:00
-- url     : https://prove2.me/submissions/9d9b878b-1917-4adb-8ac6-746a4cbc70df

import Theorems.Thm_mme_dwz_q6_selected_paired_induced_restricted_matrix_extraction
import Theorems.Thm_mme_cyclicSymmetrization_matrix_direct_sum_uniform_volume
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_paired_swap
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

open MME MME.DWZComponentRestriction BigOperators
universe u
set_option autoImplicit false

/-- The prescribed finite-extraction bound follows from any sufficiently
large paired-induced selection; no coloring of the full graph is required. -/
theorem solution
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
        ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  obtain ⟨a, b, c, hrestrict, hvol⟩ :=
    mme_dwz_q6_selected_paired_induced_restricted_matrix_extraction
      (K := K) s hs m L G A H family halving q index hselected
  obtain ⟨Q, a', b', c', hQ, hiso, hvol'⟩ :=
    mme_cyclicSymmetrization_matrix_direct_sum_uniform_volume (K := K) a b c hvol
  refine ⟨Q, a', b', c', ?_, ?_⟩
  · exact hiso.1.trans
      ((mme_cyclicSymmetrization_mono_restrict hrestrict).trans
        (mme_sixSymmetrization_isomorphic_cyclic_paired_swap
          (restrictedComponentPower K s m)).2)
  · have hweighted := mul_le_mul_of_nonneg_right hsize
      (Real.rpow_nonneg
        (by positivity : (0 : ℝ) ≤ ((6 ^ (4 * G + 2 * L)) ^ 3 : ℕ)) tau)
    simp only [hvol', Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, hQ, Nat.cast_pow]
    simpa only [Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using hweighted
