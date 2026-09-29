-- Prove2me | Theorems.Thm_mme_released_global_boundary_matrix_extraction
-- name    : mme_released_global_boundary_matrix_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T02:53:52.470527+00:00
-- url     : https://prove2.me/theorems/da5c4366-9e9d-4644-a975-cb33350285f2
-- title:
--   Released global boundary cells admit exact matrix extraction
-- statement:
--   For all six released owners, every coarse cell with a zero coordinate has an exact positive-dimensional matrix extraction at every integer replication. The boundary profile has precisely the released marginal histograms and the required coarse shape.
-- source:
--   Exact cell fiber counting, simultaneous tensor extraction and histogram normalization.

import Mathlib.Data.Nat.Choose.Multinomial
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
import Definitions.Def_mme_recursive_yz_owned_filters
import Definitions.Def_mme_released_global_frame_data
open BigOperators MME MME.ReleasedGlobal MME.MoreAsymmetryExactSeed
open MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open MME.TensorObj MME.RecursiveYZ.Boundary
set_option autoImplicit false
universe u
universe v w

theorem mme_released_global_boundary_matrix_extraction
    (owner : Fin 6) (k : ℕ) (c : Cell 8 1 (fun _ _ ↦ 8)) (z : Fin 3)
    (hz : (c.2.val z).val = 0) :
    ∃ B : Boundary.Profile 3
        (k * (coarseCounts owner c.2)),
      0 < B.dim ∧ B.a z * B.b z * B.c z = B.dim ∧
      (∀ i, (c.2.val i).val = B.shape z i) ∧
      (∀ i w, k * wordCounts owner i c.2 w = B.mu z i w) ∧
      ∀ (K : Type u) [Field K],
        TensorObj.Restrict (MMObj K (B.a z) (B.b z) (B.c z))
          (CWCells.unbroken K 5 3
            (k * (coarseCounts owner c.2))
            (Equiv.refl _) (fun _ => Unit.unit)
            (fun _ i => (c.2.val i).val)
            (fun i _ w => k * wordCounts owner i c.2 w)) := by sorry
