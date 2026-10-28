-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawingOn_finite_merge_iteration
-- name    : WilliamsonShmoys.planar_drawingOn_finite_merge_iteration
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:55:42.805761+00:00
-- url     : https://prove2.me/theorems/9d1360a1-e221-4579-b5f3-53d8f976eeba
-- title:
--   Iterate finite reachability merges
-- statement:
--   If every disconnected planar-drawn supergraph of the starting graph can be extended while preserving existing reachability and adding a newly reachable pair, then some planar-drawn supergraph is connected. Prove this by finite induction on the number of unreachable ordered vertex pairs: supergraph inclusion preserves reachability, while each step strictly decreases the finite unreachable-pair count. This separates the finite termination argument from the geometric component-merging work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawingOn_finite_merge_iteration
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hstep : ∀ (R : SimpleGraph V), P ≤ R →
      WilliamsonShmoys.HasPlanarDrawingOn R → ¬ R.Connected →
      ∃ S : SimpleGraph V,
        R ≤ S ∧ WilliamsonShmoys.HasPlanarDrawingOn S ∧
        (∀ u v, R.Reachable u v → S.Reachable u v) ∧
        ∃ u v, ¬ R.Reachable u v ∧ S.Reachable u v) :
    ∃ Q : SimpleGraph V,
      P ≤ Q ∧ WilliamsonShmoys.HasPlanarDrawingOn Q ∧ Q.Connected := by sorry
