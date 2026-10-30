-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_bound__p2m_316c89ef_5381_45bf_ad7e_e8d13020052b_a2
-- name    : WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_316c89ef_5381_45bf_ad7e_e8d13020052b_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:42:05.062444+00:00
-- url     : https://prove2.me/theorems/0af2d81e-eda4-4f18-8ca2-a158577f115d
-- title:
--   Maximal planar graphs meet the planar edge bound
-- statement:
--   A planar graph on at least three vertices that is maximal among planar supergraphs on the same vertex set has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_graph_edge_bound__p2m_316c89ef_5381_45bf_ad7e_e8d13020052b_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M ≤ L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (_ : DecidableRel L.Adj),
      3 * Fintype.card V - 6 ≤ L.edgeFinset.card := by sorry
