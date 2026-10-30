-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulation_completion
-- name    : WilliamsonShmoys.exists_triangulation_completion
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T00:50:42.495586+00:00
-- url     : https://prove2.me/theorems/946a4eaf-d114-4840-b3d3-4fb36f73ba29
-- title:
--   Drawable graphs admit a triangulated drawable completion
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices is a subgraph of a drawable graph on the same vertices whose edge count is exactly three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_triangulation_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hLdraw : HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V, L ≤ M ∧ HasPlanarDrawingOn M ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
