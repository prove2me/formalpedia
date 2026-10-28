-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_subset_triangulation
-- name    : WilliamsonShmoys.planar_drawing_subset_triangulation
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T22:16:23.81171+00:00
-- url     : https://prove2.me/theorems/13291b2a-4629-4728-8bdd-cacc5f8bbca4
-- title:
--   Triangulate a drawn finite vertex subset on the sphere
-- statement:
--   This geometric child has no root, prescribed paths, or bags. Restrict the drawing to S, obtain a finite rotation system through a topological regular-neighborhood or polygonalization argument, and augment to an edge-maximal simple planar graph on the same vertices. With at least three vertices, its spherical faces are triangles. Orient their boundaries consistently, enumerate faces, and apply Euler's formula together with three sides per face and two darts per edge. Disconnected subsets may first be joined in complementary regions. The threshold three is essential; the three-vertex case has two oppositely oriented faces. This drawing-to-map conversion remains substantial formalization work.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_TriangularMap

theorem WilliamsonShmoys.planar_drawing_subset_triangulation
    {n : Nat} (G : SimpleGraph (Fin n))
    (hG : WilliamsonShmoys.HasPlanarDrawing G)
    (S : Set (Fin n)) [Fintype S] (hS : 3 ≤ Fintype.card S) :
    ∃ (H : SimpleGraph S), G.induce S ≤ H ∧
      ∃ (m : Nat) (M : WilliamsonShmoys.TriangularMap H (Fin m)),
        2 * Fintype.card S = m + 4 := by sorry
