-- Prove2me | Theorems.Thm_WilliamsonShmoys_insert_edge_graph_exists__p2m_bee5e24f_cd5c_4379_8d98_415a22bc9c47_a2
-- name    : WilliamsonShmoys.insert_edge_graph_exists__p2m_bee5e24f_cd5c_4379_8d98_415a22bc9c47_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T04:32:12.438701+00:00
-- url     : https://prove2.me/theorems/e6252305-dd78-4cc5-acd9-da4b76f8d4e8
-- title:
--   Construct a graph by adding an edge with distinct endpoints
-- statement:
--   Construct a simple graph containing H whose edges are exactly the edges of H together with the undirected pair {u,v}, assuming the endpoints are distinct.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.insert_edge_graph_exists__p2m_bee5e24f_cd5c_4379_8d98_415a22bc9c47_a2 {V : Type} [Fintype V] [LinearOrder V] (H : SimpleGraph V) (u v : V) (huv : u ≠ v) : ∃ G : SimpleGraph V, H ≤ G ∧ G.Adj u v ∧ ∀ x y, G.Adj x y ↔ H.Adj x y ∨ (x = u ∧ y = v) ∨ (x = v ∧ y = u) := by sorry
