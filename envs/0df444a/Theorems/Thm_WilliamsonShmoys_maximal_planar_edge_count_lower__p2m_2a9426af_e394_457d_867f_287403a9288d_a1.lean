-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower__p2m_2a9426af_e394_457d_867f_287403a9288d_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_2a9426af_e394_457d_867f_287403a9288d_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:02:20.502595+00:00
-- url     : https://prove2.me/theorems/2a979728-50d2-4a09-b4b8-e239f7e565fc
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   An inclusion-maximal graph drawable on the same finite vertex type, with at least three vertices, has at least `3n - 6` edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower__p2m_2a9426af_e394_457d_867f_287403a9288d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (hcard : 3 ≤ Fintype.card V) (H : SimpleGraph V)
    (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj := fun G => Classical.decRel G.Adj
    3 * Fintype.card V - 6 ≤ H.edgeFinset.card := by sorry
