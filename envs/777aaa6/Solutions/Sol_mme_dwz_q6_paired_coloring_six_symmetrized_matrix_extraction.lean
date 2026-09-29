-- Prove2me | solution 1 for mme_dwz_q6_paired_coloring_six_symmetrized_matrix_extraction
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T01:46:36.22073+00:00
-- url     : https://prove2.me/submissions/9e6a2f61-79e9-4279-b286-65e26a7a459c

import Theorems.Thm_mme_cyclicSymmetrization_matrix_direct_sum_uniform_volume
import Theorems.Thm_mme_dwz_q6_paired_coloring_restricted_matrix_direct_sum_extraction
import Theorems.Thm_mme_sixSymmetrization_isomorphic_cyclic_paired_swap
import Theorems.Thm_mme_cyclicSymmetrization_mono_restrict

open MME MME.DWZComponentRestriction
universe u
set_option autoImplicit false

/-- A proper paired-conflict coloring gives a cubic number of matrix blocks
from the six-fold symmetrized literal restricted component power. -/
theorem solution
    {K : Type u} [Field K] (s : Fin 15) (hs : s = 13 ∨ s = 14)
    (m L G A H : ℕ) {k : ℕ}
    (family : CWQ6PrimaryHashFamily (DWZTable2Counts.component s * m) L G A H)
    (halving : family.CommonBalancedXYHalving) (hk : 0 < k)
    (coloring : (family.pairedCyclicConflictGraph halving).Coloring (Fin k)) :
    ∃ (Q : ℕ) (a b c : Fin Q → ℕ),
      A ^ 3 * H ^ 3 ≤ k ^ 3 * Q ∧
      TensorObj.Restrict (TensorObj.bigAdd (fun j ↦ MMObj K (a j) (b j) (c j)))
        (sixSymmetrization (restrictedComponentPower K s m)) ∧
      ∀ j, a j * b j * c j = (6 ^ (4 * G + 2 * L)) ^ 3 := by
  obtain ⟨q, a, b, c, hcount, hrestrict, hvol⟩ :=
    mme_dwz_q6_paired_coloring_restricted_matrix_direct_sum_extraction
      (K := K) s hs m L G A H family halving hk coloring
  obtain ⟨Q, a', b', c', hQ, hiso, hvol'⟩ :=
    mme_cyclicSymmetrization_matrix_direct_sum_uniform_volume (K := K) a b c hvol
  refine ⟨Q, a', b', c', ?_, ?_, hvol'⟩
  · have h := Nat.pow_le_pow_left hcount 3
    simpa only [mul_pow, ← hQ] using h
  · exact hiso.1.trans
      ((mme_cyclicSymmetrization_mono_restrict hrestrict).trans
        (mme_sixSymmetrization_isomorphic_cyclic_paired_swap
          (restrictedComponentPower K s m)).2)
