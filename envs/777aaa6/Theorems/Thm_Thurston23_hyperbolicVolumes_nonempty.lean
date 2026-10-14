-- Prove2me | Theorems.Thm_Thurston23_hyperbolicVolumes_nonempty
-- name    : Thurston23.hyperbolicVolumes_nonempty
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-05T22:57:20.57948+00:00
-- url     : https://prove2.me/theorems/37f6756d-96c5-441a-9b43-a672ceb004ca
-- title:
--   Milestone 2 - some finite-volume hyperbolic 3-manifold exists
-- statement:
--   The set of volumes is nonempty: there is a Kleinian action with a fundamental domain of finite positive measure. Without this the goal would be vacuously false rather than open. This is a substantial target in its own right: it asks for a concrete cofinite-volume Kleinian group, and Mathlib has no hyperbolic 3-space, no isometry group of it, and no action of PSL(2,C) on the upper half-space.
-- source:
--   Classical; e.g. the Bianchi groups PSL(2,O_d), or the figure-eight knot group.

import Definitions.Def_Thurston23_bundle

namespace Thurston23

open MeasureTheory

/-- **Milestone 2.** There is at least one finite-volume hyperbolic
`3`-manifold, so the set of volumes is nonempty. Without this the goal below
would be vacuously false rather than open. This is not a warm-up: it asks for a
concrete cofinite-volume Kleinian group together with a fundamental domain of
finite positive measure, and Mathlib has no `ℍ³`, no `Isom(ℍ³)` and no action of
`PSL(2,ℂ)` on the upper half-space. -/
theorem hyperbolicVolumes_nonempty : hyperbolicVolumes.Nonempty := by
  sorry

end Thurston23
