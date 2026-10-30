-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_87f8bddb_6da2_4d95_81aa_1f835ee1c5bb_a3
-- name    : WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_87f8bddb_6da2_4d95_81aa_1f835ee1c5bb_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:23:01.120989+00:00
-- url     : https://prove2.me/theorems/b47519ab-fd46-4650-ab67-493cc220d1f4
-- title:
--   Simple planar graph edge bound from arc drawing
-- statement:
--   A connected simple graph with at least three vertices and the supplied crossing-free arc drawing has at most 3|V| − 6 edges. This child isolates the remaining planar topology needed by the parent; the parent chooses f = |E| − |V| + 2 and derives the target equations and inequalities arithmetically.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_87f8bddb_6da2_4d95_81aa_1f835ee1c5bb_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hConn : N.Connected) (hDraw : HasPlanarDrawingOn N) :
    (N.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by sorry
