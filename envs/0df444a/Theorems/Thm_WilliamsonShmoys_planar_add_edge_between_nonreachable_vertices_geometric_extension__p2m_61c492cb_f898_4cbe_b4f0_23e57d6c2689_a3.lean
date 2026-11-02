-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_nonreachable_vertices_geometric_extension__p2m_61c492cb_f898_4cbe_b4f0_23e57d6c2689_a3
-- name    : WilliamsonShmoys.planar_add_edge_between_nonreachable_vertices_geometric_extension__p2m_61c492cb_f898_4cbe_b4f0_23e57d6c2689_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T17:27:50.364836+00:00
-- url     : https://prove2.me/theorems/495cac58-7490-446f-8100-da61c3d7cced
-- title:
--   Extend a planar drawing across distinct components
-- statement:
--   If a finite graph with a drawing has two vertices in different connected components, there is a drawable supergraph containing the edge between those vertices; that edge was absent from the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_add_edge_between_nonreachable_vertices_geometric_extension__p2m_61c492cb_f898_4cbe_b4f0_23e57d6c2689_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (u v : V)
    (hsep : ¬ N.Reachable u v) (hN : HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V, N ≤ P ∧ P.Adj u v ∧ ¬ N.Adj u v ∧ HasPlanarDrawingOn P := by sorry
