-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_exact_edge_count__p2m_00590216_3bdf_4c63_b52e_9e355ea90f1e_a1
-- name    : WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_00590216_3bdf_4c63_b52e_9e355ea90f1e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T22:14:26.415232+00:00
-- url     : https://prove2.me/theorems/dbf7c19f-18a9-4ddb-bdc9-64443a6c5a07
-- title:
--   Planar supergraph with exact maximal edge count
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertex type with exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_exact_edge_count__p2m_00590216_3bdf_4c63_b52e_9e355ea90f1e_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hKplanar : WilliamsonShmoys.HasPlanarDrawingOn K) (hV : 3 ≤ Fintype.card V) : ∃ L : SimpleGraph V, LE.le K L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧ 3 * Fintype.card V - 6 = L.edgeSet.ncard := by sorry
