-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_edge_lower_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
-- name    : WilliamsonShmoys.planar_drawing_connected_edge_lower_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:35:26.010692+00:00
-- url     : https://prove2.me/theorems/31018b56-35c8-4565-a20e-e4220d23a809
-- title:
--   Connected finite graphs have enough edges
-- statement:
--   This child supplies the lower edge bound used to make the face index type nonempty. Its source is the spanning-tree argument for a finite connected graph. A proof can obtain a spanning tree, use that a tree on the vertex type has |V| - 1 edges, and show its edges belong to G. Connectedness rules out the empty graph, so the bound also handles the smallest connected cases.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_edge_lower_bound__p2m_bc9cd380_c5b9_4141_b573_8fb0410f4911_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (dG : DecidableRel G.Adj)
    (hConn : G.Connected) :
    Fintype.card V ≤ (letI : DecidableRel G.Adj := dG; G.edgeFinset.card) + 1 := by sorry
