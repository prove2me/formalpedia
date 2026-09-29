-- Prove2me | solution 1 for EmergentGeometry.matching_ER_EPR
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:59:25.18856+00:00
-- url     : https://prove2.me/submissions/0bdf4b57-d4b8-412c-8c59-3b9775e23cac

-- Sol generated from Novelty/EREPRQuantumBridge.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRQuantumBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Theorems.Thm_EmergentGeometry_matching_path_fst
import Theorems.Thm_EmergentGeometry_mutualInfo_eq_zero_of_no_bridge
import Theorems.Thm_EmergentGeometry_weight_eq_half_mutualInfo

/-!
# From qubits to throats: quantitative ER=EPR for many Bell pairs

`Novelty.EREPRBridge` matches a single entangled qubit pair with a single bulk
throat.  This file makes the dictionary quantitative and extends it to many
pairs.

* `linearEntropy_eq_concurrence_sq`: for a normalised real two-qubit pure state
  the *linear entanglement entropy* `2(1 - Tr ρ²)` of either marginal equals the
  square of the concurrence.  Hence the throat area assigned to the pair in the
  ER=EPR dictionary is exactly the square root of the linear entropy of the
  state, and `mutualInfo² = 4 · linearEntropy`.

* `matchingModel`: the bulk geometry of `n` independent Bell pairs, a perfect
  matching of `2n` boundary cells by throats of prescribed areas.  We prove that
  partners have mutual information twice the throat area
  (`matching_partner_mutualInfo`), that non-partners are exactly unentangled
  (`matching_cross_mutualInfo`), that a bridge joins two cells precisely when
  they are partners with a positive throat (`matching_bridge_iff`), and that the
  whole geometry is reconstructed from the pairwise entanglement data
  (`matching_reconstruction`).
-/

noncomputable section

open EmergentGeometry

open Finset EmergentSpacetime

/-! ## Linear entanglement entropy of a real two-qubit state -/





/-! ## The geometry of `n` Bell pairs -/

variable {n : ℕ}


lemma matchingModel_noBulk (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) :
    NoBulk (matchingModel w hw) := fun _ => rfl




/-- **Non-partners are exactly unentangled**: cells belonging to different Bell
pairs have vanishing mutual information, because no bulk bridge joins them. -/
theorem matching_cross_mutualInfo (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i)
    {i j : Fin n} (hij : i ≠ j) (b c : Bool) :
    mutualInfo (matchingModel w hw) (single (i, b)) (single (j, c)) = 0 := by
  refine mutualInfo_eq_zero_of_no_bridge _ _ ?_
  intro p q hp hq hpath
  have hp' : p = (i, b) := by simpa [single] using hp
  have hq' : q = (j, c) := by simpa [single] using hq
  subst hp'; subst hq'
  exact hij (matching_path_fst hpath)





open EmergentGeometry in
theorem solution(w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (i j : Fin n) (b c : Bool) :
    (i = j ∧ b ≠ c ∧ 0 < w i →
        BulkPath (matchingModel w hw).toBulkGraph (i, b) (j, c) ∧
        0 < mutualInfo (matchingModel w hw) (single (i, b)) (single (j, c)))
      ∧ (i ≠ j →
        ¬ BulkPath (matchingModel w hw).toBulkGraph (i, b) (j, c) ∧
        mutualInfo (matchingModel w hw) (single (i, b)) (single (j, c)) = 0) := by
  constructor
  · rintro ⟨rfl, hbc, hpos⟩
    have hb : b = !c := by cases b <;> cases c <;> simp_all
    have hstep : BulkPath (matchingModel w hw).toBulkGraph (i, b) (i, c) := by
      refine Relation.ReflTransGen.single ?_
      show (0:ℝ) < (matchingModel w hw).weight (i, b) (i, c)
      have : (matchingModel w hw).weight (i, b) (i, c) = w i := by
        simp [matchingModel, hbc]
      rw [this]; exact hpos
    refine ⟨hstep, ?_⟩
    have hne : ((i, b) : Fin n × Bool) ≠ (i, c) := by simp [hbc]
    have h := weight_eq_half_mutualInfo (matchingModel_noBulk w hw) hne
    have hval : (matchingModel w hw).weight (i, b) (i, c) = w i := by
      simp [matchingModel, hbc]
    rw [hval] at h
    linarith
  · intro hij
    refine ⟨fun hpath => hij (matching_path_fst hpath), matching_cross_mutualInfo w hw hij b c⟩
