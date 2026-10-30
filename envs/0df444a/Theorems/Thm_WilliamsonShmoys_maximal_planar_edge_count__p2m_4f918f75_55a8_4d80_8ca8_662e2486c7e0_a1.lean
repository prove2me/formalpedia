-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4f918f75_55a8_4d80_8ca8_662e2486c7e0_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_4f918f75_55a8_4d80_8ca8_662e2486c7e0_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T07:21:02.761355+00:00
-- url     : https://prove2.me/theorems/1112e69e-48a4-4643-92d8-b48cd86b06af
-- title:
--   Edge count of a maximal drawable simple graph
-- statement:
--   A finite simple graph with a crossing-free drawing that is maximal among drawable supergraphs on the same vertex set, and with at least three vertices, has exactly 3V − 6 edges. The statement includes the three-vertex case, where maximality gives the triangle. Derive it by forming a plane embedding from the drawing, using maximality to rule out faces with a drawable diagonal, and applying Euler’s formula and the face-edge incidence count. This removes the topological counting argument from the parent; the remaining core obligation is proving those embedding and triangulation facts from the exact arc predicates.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_4f918f75_55a8_4d80_8ca8_662e2486c7e0_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (C : L.ConnectedComponent)
    (M : SimpleGraph C.supp)
    [Fintype C.supp]
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMax : ∀ N : SimpleGraph C.supp, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M)
    (hcard : 3 ≤ C.supp.ncard) :
    M.edgeSet.ncard + 6 = 3 * C.supp.ncard := by sorry
