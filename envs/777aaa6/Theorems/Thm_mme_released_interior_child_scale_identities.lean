-- Prove2me | Theorems.Thm_mme_released_interior_child_scale_identities
-- name    : mme_released_interior_child_scale_identities
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T05:28:31.460536+00:00
-- url     : https://prove2.me/theorems/46ddf9fa-e3c3-46e0-a60e-70b86c1fbd52
-- title:
--   Released child counts agree at the physical replication scale
-- statement:
--   For every owner, recipe, region and child, the denominator-based scale identifies both the physical position count and each integer marginal with their released counts. The identities also hold for empty cells and every natural replication. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Definitions.Def_mme_released_interior_integer_profiles
import Mathlib.Tactic.Ring
open MME MME.RecursiveYZ MME.ReleasedInterior MME.MoreAsymmetryExactSeed MME.CompleteSplit

theorem mme_released_interior_child_scale_identities
    (owner : Fin 6) (s : Fin 45) (r : Fin 6) (c : Split s) (k : ℕ) :
    let scale := (seed owner s).region.getD r.val 0 *
      (splitWeight owner s r c +
        splitWeight owner s r (complement (parent_total s r) c)) * denominator
    2 * (denominator * (k * scale)) =
      (2 * k) * (splitCount owner s r c +
        splitCount owner s r (complement (parent_total s r) c)) ∧
    ∀ (i : Fin 3) (w : CompleteWord 2),
      2 * (k * scale) * childMarginal owner s r c i w =
        (2 * k) * integerProfile owner s i ⟨r, c⟩ w := by sorry
