-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_graph_connected__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
-- name    : WilliamsonShmoys.maximal_drawable_graph_connected__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T01:47:51.712821+00:00
-- url     : https://prove2.me/theorems/53c320f3-e91d-4263-a564-4632ae783af5
-- title:
--   A maximal drawable graph is connected
-- statement:
--   A maximal drawable graph with at least three vertices is connected. The source is the standard planar extension argument: if the graph is disconnected, join components with an edge while preserving a crossing-free drawing, contradicting maximality. This carries the main topological obligation of the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_graph_connected__p2m_a79da144_fcf1_49a7_8693_9dcdff9b3064_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N ≤ M) :
    M.Connected := by sorry
