-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_fdaf46ab_4488_466d_ade5_afe997f74795_a1
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_fdaf46ab_4488_466d_ade5_afe997f74795_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:58:34.289197+00:00
-- url     : https://prove2.me/theorems/6387f002-1fd9-417d-811a-77c2c095c6e5
-- title:
--   Extension of a planar drawing to a maximal planar graph
-- statement:
--   Every finite simple graph with at least three vertices and a crossing-free drawing extends, on the same vertex set, to a crossing-free simple graph containing all its edges and having exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_fdaf46ab_4488_466d_ade5_afe997f74795_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    letI : DecidableRel G.Adj := Classical.decRel G.Adj
    ∃ H : SimpleGraph V,
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       G.edgeFinset.card <= H.edgeFinset.card) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj
       H.edgeFinset.card + 6 = 3 * Fintype.card V) := by sorry
