-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_lower_bound__p2m_88a12398_1857_4cda_a49a_bb014d1d3fb8_a3
-- name    : WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_88a12398_1857_4cda_a49a_bb014d1d3fb8_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:01:01.256485+00:00
-- url     : https://prove2.me/theorems/fcfb21bb-7adb-48c4-98c9-78175b7ac091
-- title:
--   Spanning planar extension reaches the planar edge bound
-- statement:
--   Every drawable simple graph on at least three finite ordered vertices has a drawable supergraph on the same vertex type with at least 3|V|−6 edges. This supplies the augmentation needed by the parent; hmax then identifies the extension with M. The n = 3 boundary gives a zero lower bound. A proof route is to augment the drawing to a maximal planar graph on the same vertices and derive the count from Euler’s formula, with disconnected components handled explicitly. The existing a1 dependency has this same mathematical obligation but remains Open, so the earlier direct proof could not use it as a proved dependency.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_edge_lower_bound__p2m_88a12398_1857_4cda_a49a_bb014d1d3fb8_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    Exists fun N : SimpleGraph V =>
      (forall {u v : V}, M.Adj u v -> N.Adj u v) /\
      WilliamsonShmoys.HasPlanarDrawingOn N /\
      (letI : DecidableRel N.Adj := Classical.decRel N.Adj
       3 * Fintype.card V - 6 <= N.edgeFinset.card) := by sorry
