-- Prove2me | Theorems.Thm_Hirsch_scalar_height_fiber_diameter_linear
-- name    : Hirsch.scalar_height_fiber_diameter_linear
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-08T16:39:12.271138+00:00
-- url     : https://prove2.me/theorems/b372d4fc-5bbd-4d32-96fc-d6d560d70422
-- title:
--   Affine scalar-height fibers of fixed bounded seeds have linear graph diameter
-- statement:
--   For finitely many nonempty compact convex seed polytopes with at most v_i vertices and e_i undirected edges, represented by explicit finite covers, the common affine-height fiber has graph diameter at most sum_i (3*v_i + e_i - 1). This is the general scalar-fiber obstruction proved mathematically in prove2me-work PR #11: descend both endpoints to the common bottom level, then route in the product of bottom sections. For k Q28 copies (274 vertices, 720 edges each), the bound is 1541k. Thus arbitrary scalar-height choices on fixed seeds cannot yield a superpolynomial family. This is an Open Lean formalization target, not a literature-priority claim.
-- source:
--   Original mathematical argument developed in jjoshua2/prove2me-work PR #11 (2026-09-08); no literature-priority claim.

import Definitions.Def_Hirsch_scalar_fiber_model
set_option autoImplicit false
open scoped RealInnerProductSpace BigOperators

theorem Hirsch.scalar_height_fiber_diameter_linear :
    ∀ (k d : ℕ)
      (P : Fin k → Set (EuclideanSpace ℝ (Fin d)))
      (h : Fin k → EuclideanSpace ℝ (Fin d) →ᵃ[ℝ] ℝ)
      (v e : Fin k → ℕ),
      (∀ i, Convex ℝ (P i)) →
      (∀ i, IsCompact (P i)) →
      (∀ i, (P i).Nonempty) →
      (∀ i, Hirsch.VertexCover (P i) (v i)) →
      (∀ i, Hirsch.EdgeCover (P i) (e i)) →
      Hirsch.DiamLE (Hirsch.ScalarHeightFiber P h)
        (∑ i, (3 * v i + e i - 1)) := by sorry
