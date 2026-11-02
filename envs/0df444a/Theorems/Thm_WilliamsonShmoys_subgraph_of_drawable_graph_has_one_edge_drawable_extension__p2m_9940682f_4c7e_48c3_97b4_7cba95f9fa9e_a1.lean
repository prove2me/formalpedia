-- Prove2me | Theorems.Thm_WilliamsonShmoys_subgraph_of_drawable_graph_has_one_edge_drawable_extension__p2m_9940682f_4c7e_48c3_97b4_7cba95f9fa9e_a1
-- name    : WilliamsonShmoys.subgraph_of_drawable_graph_has_one_edge_drawable_extension__p2m_9940682f_4c7e_48c3_97b4_7cba95f9fa9e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T12:49:53.892014+00:00
-- url     : https://prove2.me/theorems/7d2fbe79-8bd6-4aad-91b3-d89558965ee5
-- title:
--   A strict drawable supergraph yields a drawable one-edge extension
-- statement:
--   If a drawable graph $L$ contains $K$ and has more edges, some edge of $L$ is missing from $K$. Adding that edge to $K$ gives a drawable graph: restrict the drawing of $L$ to the edges of the resulting graph. This removes finite edge extraction and drawing restriction from the parent; it does not require maximality or the planar edge bound.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Operations

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.subgraph_of_drawable_graph_has_one_edge_drawable_extension__p2m_9940682f_4c7e_48c3_97b4_7cba95f9fa9e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K L : SimpleGraph V) [DecidableRel K.Adj] [DecidableRel L.Adj]
    (hKL : K ≤ L)
    (hL : HasPlanarDrawingOn L)
    (hcard : K.edgeFinset.card < L.edgeFinset.card) :
    ∃ u v, ¬ K.Adj u v ∧
      (K ⊔ SimpleGraph.edge u v).Adj u v ∧
      HasPlanarDrawingOn (K ⊔ SimpleGraph.edge u v) := by sorry
