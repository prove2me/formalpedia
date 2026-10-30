-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_graph_add_bridge__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2
-- name    : WilliamsonShmoys.planar_graph_add_bridge__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T23:44:17.167419+00:00
-- url     : https://prove2.me/theorems/0429bc33-fbf6-41dd-a067-66ab7d02dd4c
-- title:
--   Add a planar bridge between distinct components
-- statement:
--   If two vertices are in distinct reachability components of a finite planar graph, adding exactly the edge between them yields a planar supergraph. This isolates the topological work used by the parent. A proof route redraws the two components with the selected endpoints incident to their outer faces, separates the drawings, and routes the new arc through the exterior. Since reachability is reflexive, the endpoints are distinct; since they are unreachable, the new edge was not already present. The remaining core obligation is formalizing this redraw-and-arc construction for the exact drawing predicate.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_graph_add_bridge__p2m_e87f3d6d_f5ac_4caa_95af_19e806d71ee4_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (x y : V)
    (hxy : ¬ G.Reachable x y) :
    ∃ N : SimpleGraph V,
      G ≤ N ∧
      (∀ u v, N.Adj u v ↔
        G.Adj u v ∨ ((u = x ∧ v = y) ∨ (u = y ∧ v = x))) ∧
      HasPlanarDrawingOn N := by
  sorry
