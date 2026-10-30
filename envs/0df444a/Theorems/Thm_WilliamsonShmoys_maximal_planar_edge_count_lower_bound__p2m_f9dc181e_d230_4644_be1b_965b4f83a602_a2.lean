-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_f9dc181e_d230_4644_be1b_965b4f83a602_a2
-- name    : WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f9dc181e_d230_4644_be1b_965b4f83a602_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:00:42.673841+00:00
-- url     : https://prove2.me/theorems/c7faf2fe-bfe2-4bd3-9a36-edfb3235a50d
-- title:
--   Maximal planar edge count lower bound
-- statement:
--   For a drawable graph on at least three vertices that is maximal among drawable supergraphs on the same vertex type, the edge count is at least 3|V|−6. This is a new argument from the drawing definition: the supplied maximality makes every drawable supergraph equal to K; establish connectedness and triangular faces for such a maximal plane graph, then combine Euler’s formula with the edge-face incidence count. It removes the target’s lower-bound obligation. The core remaining work is formalizing those topological facts for the given continuous arcs; the size and maximality hypotheses are preserved, including the three-vertex case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_f9dc181e_d230_4644_be1b_965b4f83a602_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K)
    (hV : LE.le 3 (Fintype.card V))
    (hmax : (L : SimpleGraph V) -> LE.le K L -> HasPlanarDrawingOn L -> LE.le L K) :
    LE.le (3 * Fintype.card V) (K.edgeSet.ncard + 6) := by
  sorry
