-- Prove2me | Theorems.Thm_WilliamsonShmoys_edge_count_maximal_planar__p2m_7b8c7f37_b8de_44ac_bf27_503e942d415a_a3
-- name    : WilliamsonShmoys.edge_count_maximal_planar__p2m_7b8c7f37_b8de_44ac_bf27_503e942d415a_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T21:49:14.673623+00:00
-- url     : https://prove2.me/theorems/8fdb4f78-7a22-4d46-bd0b-609fa5b74b25
-- title:
--   Edge count of an edge-maximal finite planar graph
-- statement:
--   An edge-maximal finite simple graph with the specified planar drawing and at least three vertices has exactly 3|V| − 6 edges. The proof route is to establish connectedness and triangular faces from maximality, then combine Euler’s formula with face-edge incidence counting.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.edge_count_maximal_planar__p2m_7b8c7f37_b8de_44ac_bf27_503e942d415a_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
