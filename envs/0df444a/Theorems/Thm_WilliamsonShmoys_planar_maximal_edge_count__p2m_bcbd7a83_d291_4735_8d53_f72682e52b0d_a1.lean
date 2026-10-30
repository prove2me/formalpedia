-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_count__p2m_bcbd7a83_d291_4735_8d53_f72682e52b0d_a1
-- name    : WilliamsonShmoys.planar_maximal_edge_count__p2m_bcbd7a83_d291_4735_8d53_f72682e52b0d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:35:17.655267+00:00
-- url     : https://prove2.me/theorems/55144396-2551-4844-a692-ea08946a9a50
-- title:
--   Edge count of an edge-maximal planar graph
-- statement:
--   An edge-maximal graph with this planar drawing on at least three vertices has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_edge_count__p2m_bcbd7a83_d291_4735_8d53_f72682e52b0d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (hN : HasPlanarDrawingOn N)
    (hmax : ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N)
    (hcard : 3 ≤ Fintype.card V) :
    (letI : DecidableRel N.Adj := dN;
      N.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
