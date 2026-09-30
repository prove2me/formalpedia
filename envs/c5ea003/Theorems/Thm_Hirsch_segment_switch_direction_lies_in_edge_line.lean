-- Prove2me | Theorems.Thm_Hirsch_segment_switch_direction_lies_in_edge_line
-- name    : Hirsch.segment_switch_direction_lies_in_edge_line
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-13T19:12:20.178963+00:00
-- url     : https://prove2.me/theorems/eee91000-7740-47bb-8883-303998b601ea
-- title:
--   A changing segment allocation forces the segment direction into the common edge line
-- statement:
--   Let x and y lie on all of a family of common tight hyperplanes. Suppose the common kernel of those rows is exactly the line spanned by y-x. If a positive segment in direction g can be moved forward from x and backward from y while remaining feasible for all those rows, then g must lie in that same line. In a polytope application, this says that when a Minkowski segment factor switches endpoint allocation across an ordinary edge, its direction is parallel to that edge.
-- source:
--   Standalone proof extracted from PR #210 antipodal segment-discovery work: https://github.com/jjoshua2/prove2me-work/blob/formal/dual-wall-carrier-routing/research/publication_packets/pr210_catchup/segment_switch_edge_line/solution.lean

import Mathlib

theorem Hirsch.segment_switch_direction_lies_in_edge_line
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    {ι : Type*} (a : ι → E →ₗ[ℝ] ℝ) (b : ι → ℝ)
    (τ : ℝ) (x y g : E) (hτ : 0 < τ)
    (hx : ∀ i, a i x = b i) (hy : ∀ i, a i y = b i)
    (hforward : ∀ i, a i (x + τ • g) ≤ b i)
    (hbackward : ∀ i, a i (y - τ • g) ≤ b i)
    (hkernel : ∀ z : E, (∀ i, a i z = 0) → ∃ r : ℝ, z = r • (y-x)) :
    ∃ r : ℝ, g = r • (y-x) := by sorry
