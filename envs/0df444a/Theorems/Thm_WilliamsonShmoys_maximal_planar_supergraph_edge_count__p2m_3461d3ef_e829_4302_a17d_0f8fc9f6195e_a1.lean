-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_3461d3ef_e829_4302_a17d_0f8fc9f6195e_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_3461d3ef_e829_4302_a17d_0f8fc9f6195e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:58:58.436421+00:00
-- url     : https://prove2.me/theorems/f0a3ab30-d303-4240-9967-550b6cb40a95
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   An inclusion-maximal drawable simple graph on a finite vertex type with at least three vertices has exactly $3|V|-6$ edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_3461d3ef_e829_4302_a17d_0f8fc9f6195e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (J : SimpleGraph V) (hJ : HasPlanarDrawingOn J)
    (hmax : forall K : SimpleGraph V,
      HasPlanarDrawingOn K -> J <= K -> K <= J)
    (hcard : 3 <= Fintype.card V) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    J.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
