-- Prove2me | solution 1 for EmergentGeometry.matching_path_fst
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:56:20.917419+00:00
-- url     : https://prove2.me/submissions/cda6cf88-289d-4b31-8e29-67fbeda21786

-- Sol generated from Novelty/EREPRQuantumBridge.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRQuantumBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone

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




/-- Positive-area steps in the matching geometry never leave a pair. -/
lemma matching_adj_fst {w : Fin n → ℝ} {hw : ∀ i, 0 ≤ w i} {p q : Fin n × Bool}
    (h : BulkAdj (matchingModel w hw).toBulkGraph p q) : p.1 = q.1 := by
  by_contra hne
  have : (matchingModel w hw).weight p q = 0 := by
    simp only [matchingModel]
    exact if_neg (fun hh => hne hh.1)
  rw [BulkAdj, this] at h
  exact lt_irrefl 0 h







open EmergentGeometry in
theorem solution{w : Fin n → ℝ} {hw : ∀ i, 0 ≤ w i} {p q : Fin n × Bool}
    (h : BulkPath (matchingModel w hw).toBulkGraph p q) : p.1 = q.1 := by
  induction h with
  | refl => rfl
  | tail _ hlast ih => exact ih.trans (matching_adj_fst hlast)
