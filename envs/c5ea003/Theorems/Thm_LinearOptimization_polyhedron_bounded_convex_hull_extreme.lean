-- Prove2me | Theorems.Thm_LinearOptimization_polyhedron_bounded_convex_hull_extreme
-- name    : LinearOptimization.polyhedron_bounded_convex_hull_extreme
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-05T20:48:26.73514+00:00
-- url     : https://prove2.me/theorems/318b468f-42ab-4f12-b19b-e98e0ec904dd
-- title:
--   A nonempty bounded polyhedron is the convex hull of its extreme points
-- statement:
--   **(Theorem 2.9 = Corollary 4.4)** A nonempty and bounded polyhedron is the convex hull of its extreme points.
-- source:
--   Bertsimas & Tsitsiklis, Introduction to Linear Optimization, Athena Scientific, 1997, Theorem 2.9, p. 68; restated as Corollary 4.4, p. 182

import Mathlib.Analysis.Convex.Hull
import Mathlib.Analysis.Convex.Extreme
import Definitions.Def_Polyhedron


/-- **Bertsimas & Tsitsiklis, Theorem 2.9 (p. 68) = Corollary 4.4 (p. 182).** A nonempty
bounded polyhedron equals the convex hull of its extreme points. -/

theorem LinearOptimization.polyhedron_bounded_convex_hull_extreme {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (hne : (polyhedron A b).Nonempty)
    (hbd : IsBoundedSet (polyhedron A b)) :
    polyhedron A b =
      convexHull ℝ (Set.extremePoints ℝ (polyhedron A b)) := by
  sorry
