-- Prove2me | Theorems.Thm_Hirsch_sharp_fiber_caps_every_segment_summand
-- name    : Hirsch.sharp_fiber_caps_every_segment_summand
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T19:10:57.081063+00:00
-- url     : https://prove2.me/theorems/5e34643a-d18e-43d1-9450-24f857d966db
-- title:
--   A sharp opposing-row fiber witness caps every segment summand
-- statement:
--   Suppose a feasible point x and two inequalities pointing in opposite directions along g witness a complete parallel-fiber width exactly τ. If the whole halfspace set is any Minkowski sum of an arbitrary residual P with a segment [0,sg], then s cannot exceed τ. Thus one sharp shortest-fiber witness globally caps every segment summand in that direction, independently of how the residual is chosen.
-- source:
--   Corrected public-symbol-only packet extracted from PR #210 segment-peeling work after the earlier custom-preamble registration received WA: https://github.com/jjoshua2/prove2me-work/blob/formal/dual-wall-carrier-routing/research/publication_packets/pr210_catchup/segment_sharp_inline/solution.lean

import Mathlib
open Set

theorem Hirsch.sharp_fiber_caps_every_segment_summand
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} [Fintype ι]
    (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ) (g x : E) (τ s : ℝ)
    (i j : ι) (hi : 0 < a i g) (hj : a j g < 0)
    (hx : ∀ k, a k x ≤ b k)
    (hsharp : (-a j g)*(b i-a i x)+(a i g)*(b j-a j x) =
      τ*(a i g)*(-a j g))
    (P : Set E) (hs : 0 ≤ s)
    (hdecomp : {y : E | ∀ k, a k y ≤ b k} =
      {y : E | ∃ p ∈ P, ∃ t : ℝ, 0 ≤ t ∧ t ≤ s ∧ y = p+t • g}) : s ≤ τ := by sorry
