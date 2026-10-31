-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_90a6eb8a_5322_4ab0_9f54_46d0ab83dbd2_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_90a6eb8a_5322_4ab0_9f54_46d0ab83dbd2_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:46:10.85532+00:00
-- url     : https://prove2.me/theorems/ccd23c49-4232-4eaf-832f-2977e75f86e1
-- title:
--   Edge count of a maximal drawable planar graph
-- statement:
--   A drawable graph on at least three vertices that has no drawable strict supergraph on the same vertex type has exactly 3|V|−6 edges. The proof uses maximality to obtain triangular faces, then Euler’s formula and edge-face incidence.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_90a6eb8a_5322_4ab0_9f54_46d0ab83dbd2_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N ≤ M) :
    3 * Fintype.card V = M.edgeSet.ncard + 6 := by sorry
