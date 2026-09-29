-- Prove2me | Theorems.Thm_mme_released_interior_boundary_all_mass_volume_rate
-- name    : mme_released_interior_boundary_all_mass_volume_rate
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T06:00:59.233031+00:00
-- url     : https://prove2.me/theorems/e6462793-f9ae-4a96-950f-8dcf1059ae90
-- title:
--   Every boundary cell attains its physical volume rate
-- statement:
--   Extends the physical boundary volume rate to zero-mass cells as well as positive-mass cells, retaining the exact histogram and actual matrix restrictions over every field. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_released_interior_boundary_physical_volume_rate
open BigOperators MME MME.TensorObj MME.CompleteSplit MME.RecursiveYZ
  MME.RecursiveYZ.Boundary MME.ReleasedInterior Filter
universe u

theorem mme_released_interior_boundary_all_mass_volume_rate
    (owner : Fin 6) (s : Fin 45) (hi : (seed owner s).boundary = [])
    (c : Cell 4 6 (parent s)) (z : Fin 3) (hz : (c.2.val z).val = 0)
    (delta : ℝ) (hdelta : 0 < delta) :
    ∃ B : Boundary.Profile 2
        (splitCount owner s c.1 c.2 + splitCount owner s c.1 (complement (parent_total s c.1) c.2)),
      (∀ i w, integerProfile owner s i c w = B.mu z i w) ∧
      ∀ᶠ k : ℕ in atTop, ∃ C : Boundary.Profile 2
          (k * (splitCount owner s c.1 c.2 +
            splitCount owner s c.1 (complement (parent_total s c.1) c.2))),
        0 < C.dim ∧ C.a z * C.b z * C.c z = C.dim ∧
        (∀ i, (c.2.val i).val = C.shape z i) ∧
        (∀ i w, k * integerProfile owner s i c w = C.mu z i w) ∧
        (k : ℝ) *
          (((splitCount owner s c.1 c.2 +
              splitCount owner s c.1 (complement (parent_total s c.1) c.2) : ℕ) : ℝ) *
            Real.log 2 * mme_modern_entropyBits
              (fun w ↦ (B.count w : ℝ) /
                ((splitCount owner s c.1 c.2 +
                  splitCount owner s c.1 (complement (parent_total s c.1) c.2) : ℕ) : ℝ)) +
            ((∑ w, B.count w * ones w : ℕ) : ℝ) * Real.log 5 - delta) ≤
          Real.log (C.a z * C.b z * C.c z : ℕ) ∧
        ∀ (K : Type u) [Field K],
          TensorObj.Restrict (MMObj K (C.a z) (C.b z) (C.c z))
            (CWCells.unbroken K 5 2
              (k * (splitCount owner s c.1 c.2 +
                splitCount owner s c.1 (complement (parent_total s c.1) c.2)))
              (Equiv.refl _) (fun _ => Unit.unit)
              (fun _ i => (c.2.val i).val)
              (fun i _ w => k * integerProfile owner s i c w)) := by sorry
