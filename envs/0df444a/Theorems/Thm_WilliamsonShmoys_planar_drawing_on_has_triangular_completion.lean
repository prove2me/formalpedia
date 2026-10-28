-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_on_has_triangular_completion
-- name    : WilliamsonShmoys.planar_drawing_on_has_triangular_completion
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T22:58:41.046986+00:00
-- url     : https://prove2.me/theorems/75b79408-2fca-4d67-ab3f-00f5aac48898
-- title:
--   Planar drawing admits a triangular planar completion
-- statement:
--   Any finite graph on at least three vertices with a crossing-free drawing can be extended, on the same vertex set, to a graph that still has a crossing-free drawing and admits a finite triangular map. This isolates the geometric completion and triangulation construction; maximality is used by the parent to show the completion equals the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_TriangularMap
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

theorem WilliamsonShmoys.planar_drawing_on_has_triangular_completion
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ (K : SimpleGraph V), G ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      ∃ (m : Nat), Nonempty (WilliamsonShmoys.TriangularMap K (Fin m)) := by
  sorry
