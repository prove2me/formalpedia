-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_exact_edge_count__p2m_db3907fa_cf67_46ea_9385_43b8ffa0c261_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_db3907fa_cf67_46ea_9385_43b8ffa0c261_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:57:48.324461+00:00
-- url     : https://prove2.me/theorems/055aa8e4-db8a-47ed-b733-513d02bcef62
-- title:
--   Edge count of an edge-maximal drawable graph
-- statement:
--   An edge-inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The proof route is to show maximality forces connectedness and triangular faces, then combine Euler's formula with counting edge-face incidences. It contains the remaining topological core; the statement also covers |V|=3, where maximality forces the triangle.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_db3907fa_cf67_46ea_9385_43b8ffa0c261_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ N : SimpleGraph V,
      H.edgeSet ⊆ N.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn N →
      N.edgeSet ⊆ H.edgeSet) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
