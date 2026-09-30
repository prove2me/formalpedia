-- Prove2me | Theorems.Thm_Hirsch_any_segment_summand_le_sharp_width
-- name    : Hirsch.any_segment_summand_le_sharp_width
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T18:48:48.633353+00:00
-- url     : https://prove2.me/theorems/9f931e6d-3190-4c5d-ac47-36d4ad613fca
-- title:
--   A sharp opposing-row fiber witness caps every segment summand in that direction
-- statement:
--   Let a finite halfspace system contain a feasible point x and two rows pointing in opposite directions along g. Suppose those two rows witness that the complete g-parallel fiber through x has parameter length exactly τ. If the whole halfspace set admits any Minkowski decomposition P + [0,sg] with s nonnegative, then s ≤ τ. Thus a single sharp shortest-fiber witness upper-bounds every possible segment summand in that direction, independent of how the residual P is chosen.
-- source:
--   Standalone proof extracted from PR #210 segment-peeling work: https://github.com/jjoshua2/prove2me-work/blob/formal/dual-wall-carrier-routing/research/publication_packets/pr210_catchup/segment_sharp_maximality/solution.lean

import Mathlib
open Set
open scoped BigOperators
set_option autoImplicit false
noncomputable section
namespace HirschSegmentSharpPublic
variable {E : Type*} [AddCommGroup E] [Module ℝ E]
variable {ι : Type*} [Fintype ι]
def halfspaces (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) : Set E := {x | ∀ i, a i x ≤ b i}
def segmentSum (P : Set E) (g : E) (τ : ℝ) : Set E := {x | ∃ p ∈ P, ∃ t : ℝ, 0 ≤ t ∧ t ≤ τ ∧ x = p + t • g}
end HirschSegmentSharpPublic
end

theorem Hirsch.any_segment_summand_le_sharp_width
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g x : E) (τ s : ℝ)
    (i j : ι) (hi : 0 < a i g) (hj : a j g < 0)
    (hx : x ∈ HirschSegmentSharpPublic.halfspaces a b)
    (hsharp : (-a j g)*(b i-a i x)+(a i g)*(b j-a j x) = τ*(a i g)*(-a j g))
    (P : Set E) (hs : 0 ≤ s)
    (hdecomp : HirschSegmentSharpPublic.halfspaces a b =
      HirschSegmentSharpPublic.segmentSum P g s) : s ≤ τ := by sorry
