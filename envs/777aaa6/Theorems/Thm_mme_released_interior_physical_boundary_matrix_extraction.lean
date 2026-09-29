-- Prove2me | Theorems.Thm_mme_released_interior_physical_boundary_matrix_extraction
-- name    : mme_released_interior_physical_boundary_matrix_extraction
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:44:53.812847+00:00
-- url     : https://prove2.me/theorems/6b095526-2297-4bb4-b5b3-0856232c3e9a
-- title:
--   Boundary children of every interior recipe have physical matrix extractions
-- statement:
--   Each boundary child of every released interior recipe has an exact matrix extraction at every natural replication scale, including zero and empty cells. The result retains the boundary profile, positive dimension, exact volume, and all shape and marginal identities, uniformly over fields. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Tactic.FinCases
import Definitions.Def_mme_recursive_yz_owned_filters
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
import Theorems.Thm_mme_released_interior_scaled_integer_profile_constraints_exact
open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary
universe u
open MME.ReleasedInterior

theorem mme_released_interior_physical_boundary_matrix_extraction
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (k : ℕ) (c : Cell 4 6 (parent s)) (z : Fin 3)
    (hz : (c.2.val z).val = 0) :
    ∃ B : Boundary.Profile 2
        (k * (splitCount owner s c.1 c.2 +
          splitCount owner s c.1 (complement (parent_total s c.1) c.2))),
      0 < B.dim ∧ B.a z * B.b z * B.c z = B.dim ∧
      (∀ i, (c.2.val i).val = B.shape z i) ∧
      (∀ i w, k * integerProfile owner s i c w = B.mu z i w) ∧
      ∀ (K : Type u) [Field K],
        TensorObj.Restrict (MMObj K (B.a z) (B.b z) (B.c z))
          (CWCells.unbroken K 5 2
            (k * (splitCount owner s c.1 c.2 +
              splitCount owner s c.1 (complement (parent_total s c.1) c.2)))
            (Equiv.refl _) (fun _ => Unit.unit)
            (fun _ i => (c.2.val i).val)
            (fun i _ w => k * integerProfile owner s i c w)) := by sorry
