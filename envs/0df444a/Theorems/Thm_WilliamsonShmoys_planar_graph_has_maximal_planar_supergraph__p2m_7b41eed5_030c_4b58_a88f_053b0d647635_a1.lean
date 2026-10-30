-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_planar_supergraph__p2m_7b41eed5_030c_4b58_a88f_053b0d647635_a1
-- name    : WilliamsonShmoys.planar_graph_has_maximal_planar_supergraph__p2m_7b41eed5_030c_4b58_a88f_053b0d647635_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:01:30.05592+00:00
-- url     : https://prove2.me/theorems/ae44ef7d-5248-491f-b1a4-8fbf96ae64d7
-- title:
--   Extend a drawable graph to an inclusion-maximal drawable graph
-- statement:
--   Every drawable finite simple graph on at least three vertices is contained in a drawable graph on the same vertices that is maximal under edge inclusion among drawable graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_has_maximal_planar_supergraph__p2m_7b41eed5_030c_4b58_a88f_053b0d647635_a1 {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hL : HasPlanarDrawingOn L) : ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧ ∀ U : SimpleGraph V, T ≤ U → HasPlanarDrawingOn U → U ≤ T := by sorry
