-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:56:20.737538+00:00
-- url     : https://prove2.me/theorems/7671872f-ccc7-461e-8940-29831779f43a
-- title:
--   Edge count of a maximal planar graph
-- statement:
--   A drawable graph on at least three vertices that has no proper drawable supergraph on the same vertex type has exactly 3|V|−6 edges. The intended independent route is to establish that maximality makes the drawing's faces triangular, then formalize Euler's formula and the incidence count between faces and edges. The condition |V| ≥ 3 is necessary for this edge-count conclusion: maximal planar graphs on fewer vertices do not satisfy the displayed formula. This child isolates the geometric triangulation and counting obligation from the parent's finite maximization step.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_f852174d_ad4f_4de3_989a_32d5dda8e860_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V, H ≤ J →
      WilliamsonShmoys.HasPlanarDrawingOn J → J = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
