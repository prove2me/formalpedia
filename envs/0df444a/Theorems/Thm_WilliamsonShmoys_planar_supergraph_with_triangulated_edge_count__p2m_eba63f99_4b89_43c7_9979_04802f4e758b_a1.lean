-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_with_triangulated_edge_count__p2m_eba63f99_4b89_43c7_9979_04802f4e758b_a1
-- name    : WilliamsonShmoys.planar_supergraph_with_triangulated_edge_count__p2m_eba63f99_4b89_43c7_9979_04802f4e758b_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:51:28.194616+00:00
-- url     : https://prove2.me/theorems/7235810a-9787-44ff-bc97-6b6cda77c472
-- title:
--   Triangulated planar supergraph edge count
-- statement:
--   Every graph with a crossing-free drawing on at least three vertices is contained in a drawable graph on the same vertices whose edge count is 3n−6.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_supergraph_with_triangulated_edge_count__p2m_eba63f99_4b89_43c7_9979_04802f4e758b_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hU : HasPlanarDrawingOn U)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V, U ≤ W ∧ HasPlanarDrawingOn W ∧
      (letI : DecidableRel W.Adj := Classical.decRel W.Adj
       W.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
