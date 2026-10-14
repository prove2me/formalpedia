-- Prove2me | Theorems.Thm_Thurston23_volume_of_finite_index
-- name    : Thurston23.volume_of_finite_index
-- status  : Proved
-- author  : @t4v1
-- created : 2026-09-05T22:56:44.011938+00:00
-- url     : https://prove2.me/theorems/cfd66ea5-df83-4b44-8e21-7cbce54349c4
-- title:
--   Milestone 1 - a subgroup of index n has a fundamental domain of n times the volume
-- statement:
--   If a Kleinian group G has a subgroup H of finite index, then a fundamental domain for H has measure equal to the index times the measure of a fundamental domain for G. Equivalently, a degree n cover of a hyperbolic 3-manifold has n times its volume. This is the source of every known rational relation between volumes: commensurable manifolds have rationally related volumes, which is why the literal reading of Question 23 is false.
-- source:
--   Thurston, Bull. AMS 6 (1982), Question 23; the covering relation is classical.

import Definitions.Def_Thurston23_bundle

namespace Thurston23

open MeasureTheory

/-- **Milestone 1.** Passing to a subgroup of index `n` multiplies the volume
by `n`: a fundamental domain for `H` is the union of `n` translates of a
fundamental domain for `G`. This is the source of every known rational relation
between the volumes of hyperbolic `3`-manifolds — commensurable manifolds, that
is manifolds with a common finite cover, have rationally related volumes — and
it is what makes the literal reading of Question 23 false. Stated in `ℝ≥0∞` so
that no degenerate case is hidden by `ENNReal.ofReal`. -/
theorem volume_of_finite_index {G : Type} [Group G] [MulAction G H3]
    (hG : IsKleinian G) (H : Subgroup G) (hH : 0 < H.index)
    (F FH : Set H3) (hF : MeasureTheory.IsFundamentalDomain G F hvol)
    (hFH : MeasureTheory.IsFundamentalDomain H FH hvol) :
    hvol FH = H.index • hvol F := by
  sorry

end Thurston23
