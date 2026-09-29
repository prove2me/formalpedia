-- Prove2me | Theorems.Thm_mme_released_116_boundary_physical_volume_rate
-- name    : mme_released_116_boundary_physical_volume_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T01:17:45.734747+00:00
-- url     : https://prove2.me/theorems/41d87ebc-78e9-490f-90ea-b3b19922de4e
-- title:
--   Released boundary cells attain their physical matrix volume rate
-- statement:
--   Every released 116 boundary cell admits a base boundary profile whose three histograms equal integerProfile. For every positive tolerance, all sufficiently large replications admit positive-volume matrix extractions from the exact physical child tensor over every field, preserving the cell shape and scaled histograms. The logarithm of the matrix volume is at least replication times the base histogram entropy plus the CW-letter contribution minus tolerance.
-- source:
--   Physical boundary extraction combined with the scaled entropy volume rate.

import Mathlib.Data.Nat.Choose.Multinomial
import Theorems.Thm_mme_released_116_integer_profile_boundary
import Definitions.Def_mme_recursive_yz_owned_filters
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Definitions.Def_mme_recursive_yz_boundary_data
open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary
open MME.Released116 MME.MoreAsymmetryExactSeed
open scoped BigOperators
open Filter MME.CompleteSplit MME.RecursiveYZ.Boundary
set_option autoImplicit false
universe u

theorem mme_released_116_boundary_physical_volume_rate
    (c : Cell 4 6 parent) (z : Fin 3) (hz : (c.2.val z).val = 0)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : Boundary.Profile 2
        (splitCount c.1 c.2 + splitCount c.1 (complement (parent_total c.1) c.2)),
      (∀ i w, integerProfile i c w = B.mu z i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ C : Boundary.Profile 2
          (k * (splitCount c.1 c.2 +
            splitCount c.1 (complement (parent_total c.1) c.2))),
        0 < C.dim ∧ C.a z * C.b z * C.c z = C.dim ∧
        (∀ i, (c.2.val i).val = C.shape z i) ∧
        (∀ i w, k * integerProfile i c w = C.mu z i w) ∧
        (k : ℝ) *
          (((splitCount c.1 c.2 +
              splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ) *
            Real.log 2 * mme_modern_entropyBits
              (fun w ↦ (B.count w : ℝ) /
                ((splitCount c.1 c.2 +
                  splitCount c.1 (complement (parent_total c.1) c.2) : ℕ) : ℝ)) +
            ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta) ≤
          Real.log (C.a z * C.b z * C.c z : ℕ) ∧
        ∀ (K : Type u) [Field K],
          TensorObj.Restrict (MMObj K (C.a z) (C.b z) (C.c z))
            (CWCells.unbroken K 5 2
              (k * (splitCount c.1 c.2 +
                splitCount c.1 (complement (parent_total c.1) c.2)))
              (Equiv.refl _) (fun _ => Unit.unit)
              (fun _ i => (c.2.val i).val)
              (fun i _ w => k * integerProfile i c w)) := by sorry
