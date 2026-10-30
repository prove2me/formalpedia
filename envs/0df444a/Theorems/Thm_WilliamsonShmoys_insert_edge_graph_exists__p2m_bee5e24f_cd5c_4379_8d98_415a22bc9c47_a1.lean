-- Prove2me | Theorems.Thm_WilliamsonShmoys_insert_edge_graph_exists__p2m_bee5e24f_cd5c_4379_8d98_415a22bc9c47_a1
-- name    : WilliamsonShmoys.insert_edge_graph_exists__p2m_bee5e24f_cd5c_4379_8d98_415a22bc9c47_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-10-30T00:52:37.753155+00:00
-- url     : https://prove2.me/theorems/0ee40f97-401d-4d2f-8b2f-2db3c554b09f
-- title:
--   Construct a graph by adding one edge
-- statement:
--   Construct a simple graph whose edges are exactly the edges of H together with the undirected pair {u,v}. The result records both containment and the precise adjacency characterization needed by the geometric extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.insert_edge_graph_exists__p2m_bee5e24f_cd5c_4379_8d98_415a22bc9c47_a1 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (u v : V) : ∃ G : SimpleGraph V, H ≤ G ∧ G.Adj u v ∧ ∀ x y, G.Adj x y ↔ H.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by sorry
