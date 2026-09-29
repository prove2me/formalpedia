-- Prove2me | solution 1 for EmergentGeometry.matching_bridge_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:01:02.891142+00:00
-- url     : https://prove2.me/submissions/a436cbd1-d3ff-4fc7-93fe-be126e210e2d

-- Sol generated from Novelty/EREPRQuantumBridge.lean
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREPRQuantumBridge
import Definitions.Def_Novelty_EmergentGeometryEntropyCone
import Theorems.Thm_EmergentGeometry_matching_partner_mutualInfo
import Theorems.Thm_EmergentGeometry_matching_path_fst

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











open EmergentGeometry in
theorem solution(w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) (i : Fin n) :
    BulkPath (matchingModel w hw).toBulkGraph (i, false) (i, true) ↔ 0 < w i := by
  constructor
  · intro hp
    by_contra hnp
    have hzero : w i = 0 := le_antisymm (not_lt.1 hnp) (hw i)
    have hmi : mutualInfo (matchingModel w hw) (single (i, false)) (single (i, true)) = 0 := by
      rw [matching_partner_mutualInfo, hzero]; ring
    have hall : ∀ p q : Fin n × Bool, (matchingModel w hw).weight p q = 0 ∨ p.1 ≠ i := by
      intro p q
      by_cases hpi : p.1 = i
      · left
        by_cases h : p.1 = q.1 ∧ p.2 ≠ q.2
        · simp only [matchingModel]
          rw [if_pos h, hpi, hzero]
        · simp only [matchingModel]
          exact if_neg h
      · exact Or.inr hpi
    rcases Relation.ReflTransGen.cases_tail hp with hcon | ⟨c, hbefore, hlast⟩
    · exact absurd hcon (by simp)
    · have hc : c.1 = i := (matching_path_fst hbefore).symm
      rcases hall c (i, true) with hz | hne
      · rw [BulkAdj, hz] at hlast; exact lt_irrefl 0 hlast
      · exact hne hc
  · intro hpos
    refine Relation.ReflTransGen.single ?_
    show (0:ℝ) < (matchingModel w hw).weight (i, false) (i, true)
    simpa [matchingModel] using hpos
