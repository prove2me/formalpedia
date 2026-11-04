-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_edge_count__p2m_0e129449_44b7_4ec4_9782_615c2e23c561_a2
-- name    : WilliamsonShmoys.planar_drawing_triangulation_edge_count__p2m_0e129449_44b7_4ec4_9782_615c2e23c561_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:45:12.940359+00:00
-- url     : https://prove2.me/theorems/625bb0fc-e249-4e4e-ba10-71dd29d5fb91
-- title:
--   Triangulating a drawable graph without adding vertices
-- statement:
--   Every graph with a crossing-free drawing on a finite ordered vertex type of at least three vertices has a drawable same-vertex supergraph with exactly 3|V|−6 edges. This includes disconnected graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_triangulation_edge_count__p2m_0e129449_44b7_4ec4_9782_615c2e23c561_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V)
    : ∃ N : SimpleGraph V, ∃ dN : DecidableRel N.Adj,
        M ≤ N ∧ HasPlanarDrawingOn N ∧
        (letI : DecidableRel N.Adj := dN;
          6 * Fintype.card V = 2 * N.edgeFinset.card + 12) := by sorry
