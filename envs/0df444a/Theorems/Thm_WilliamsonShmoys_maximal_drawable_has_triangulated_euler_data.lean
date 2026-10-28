-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_has_triangulated_euler_data
-- name    : WilliamsonShmoys.maximal_drawable_has_triangulated_euler_data
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:20:38.613758+00:00
-- url     : https://prove2.me/theorems/63ad03c5-61fa-4b83-866b-5eb1485c1299
-- title:
--   Maximal drawing yields triangular face data
-- statement:
--   From the stated crossing-free arc drawing and maximality among drawable supergraphs, construct finite triangular sphere-face data for K. This removes the geometric and topological part from the parent. A proof route is to convert the arcs to a plane embedding, show maximality allows every nontriangular face to be split by adding an admissible diagonal, and establish Euler’s formula and that each edge has two incident sides. The hypothesis |V| ≥ 3 is retained, including the three-vertex boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationEulerData

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_drawable_has_triangulated_euler_data
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K) :
    Nonempty (WilliamsonShmoys.TriangulatedSphereFaceData K) := by sorry
