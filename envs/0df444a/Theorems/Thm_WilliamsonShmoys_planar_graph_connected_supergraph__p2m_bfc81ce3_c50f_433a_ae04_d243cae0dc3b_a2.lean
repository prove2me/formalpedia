-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_connected_supergraph__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a2
-- name    : WilliamsonShmoys.planar_graph_connected_supergraph__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:23:07.591514+00:00
-- url     : https://prove2.me/theorems/eae373a5-381f-465d-a90b-a76688f51574
-- title:
--   Connected planar supergraph with at least three vertices
-- statement:
--   A drawable graph on at least three vertices can be extended on the same vertices to a connected drawable graph. Its proof route joins drawing components by arcs chosen through complementary regions so they do not cross existing edges or vertices; the cardinality hypothesis excludes the empty-type counterexample to connectedness.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_graph_connected_supergraph__p2m_bfc81ce3_c50f_433a_ae04_d243cae0dc3b_a2 {V : Type} [Fintype V] [LinearOrder V] (T : SimpleGraph V) (hV : 3 ≤ Fintype.card V) (hT : WilliamsonShmoys.HasPlanarDrawingOn T) : ∃ U : SimpleGraph V, T ≤ U ∧ U.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn U := by sorry
