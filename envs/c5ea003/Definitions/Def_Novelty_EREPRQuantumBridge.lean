-- Prove2me | Definitions.Def_Novelty_EREPRQuantumBridge
-- name    : Novelty_EREPRQuantumBridge
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:21:39.19609+00:00
-- url     : https://prove2.me/theorems/7bbfe40b-45b6-43f1-b9ab-9851ad14f8fe
-- title:
--   Aether Catalog definitions — Novelty_EREPRQuantumBridge
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.EREPRQuantumBridge`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/EREPRQuantumBridge.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_EREPRBridge
import Definitions.Def_Novelty_EREqualsEPR
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

namespace EmergentGeometry

open Finset EmergentSpacetime

/-! ## Linear entanglement entropy of a real two-qubit state -/

/-- Purity `Tr ρ²` of the left marginal of a real two-qubit pure state. -/
def marginalPurity (ψ : TwoQubitState) : ℝ :=
  ∑ i, ∑ k, (leftReduced ψ i k) ^ 2

/-- Linear entanglement entropy `2(1 - Tr ρ²)` of a real two-qubit pure state. -/
def linearEntropy (ψ : TwoQubitState) : ℝ := 2 * (1 - marginalPurity ψ)



/-! ## The geometry of `n` Bell pairs -/

variable {n : ℕ}

/-- The bulk geometry of `n` independent Bell pairs: `2n` boundary cells joined
in pairs by throats of area `w i`. -/
def matchingModel (w : Fin n → ℝ) (hw : ∀ i, 0 ≤ w i) : HoloModel (Fin n × Bool) where
  weight := fun p q => if p.1 = q.1 ∧ p.2 ≠ q.2 then w p.1 else 0
  weight_symm := by
    intro p q
    by_cases h : p.1 = q.1 ∧ p.2 ≠ q.2
    · rw [if_pos h, if_pos ⟨h.1.symm, fun hh => h.2 hh.symm⟩, h.1]
    · rw [if_neg h, if_neg (fun hh => h ⟨hh.1.symm, fun k => hh.2 k.symm⟩)]
  weight_nonneg := by
    intro p q
    by_cases h : p.1 = q.1 ∧ p.2 ≠ q.2
    · rw [if_pos h]; exact hw _
    · rw [if_neg h]
  bdry := fun _ => true









end EmergentGeometry


