-- Prove2me | Theorems.Thm_EmergentGeometry_matching_path_fst
-- name    : EmergentGeometry.matching_path_fst
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:40:07.03277+00:00
-- url     : https://prove2.me/theorems/488e7655-7163-49e1-888f-df47c29e37cb
-- title:
--   Bulk paths in the matching geometry never leave a pair.
-- statement:
--   Bulk paths in the matching geometry never leave a pair.
--
--   ```lean
--   theorem EmergentGeometry.matching_path_fst{w : Fin n → ℝ} {hw : ∀ i, 0 ≤ w i} {p q : Fin n × Bool}
--       (h : BulkPath (matchingModel w hw).toBulkGraph p q) : p.1 = q.1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/EREPRQuantumBridge.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/EREPRQuantumBridge.lean#L108

-- Thm stub generated from Novelty/EREPRQuantumBridge.lean
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

theorem EmergentGeometry.matching_path_fst{w : Fin n → ℝ} {hw : ∀ i, 0 ≤ w i} {p q : Fin n × Bool}
    (h : BulkPath (matchingModel w hw).toBulkGraph p q) : p.1 = q.1 := by sorry
