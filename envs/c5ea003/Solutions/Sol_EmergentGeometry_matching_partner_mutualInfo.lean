-- Prove2me | solution 1 for EmergentGeometry.matching_partner_mutualInfo
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:59:25.992123+00:00
-- url     : https://prove2.me/submissions/2ea5853e-0b9e-4199-ae5e-a4b5f1c17855

-- Sol generated from Novelty/EREPRQuantumBridge.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRQuantumBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
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









open EmergentGeometry in
theorem solution(w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (i : Fin n) :
    mutualInfo (matchingModel w hw) (single (i, false)) (single (i, true)) = 2 * w i := by
  have hne : ((i, false) : Fin n × Bool) ≠ (i, true) := by simp
  have h := weight_eq_half_mutualInfo (matchingModel_noBulk w hw) hne
  have hval : (matchingModel w hw).weight (i, false) (i, true) = w i := by
    simp [matchingModel]
  rw [hval] at h
  linarith
