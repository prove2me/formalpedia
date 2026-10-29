-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_component_edge_extension__p2m_ae0a4a79_a73d_4cfa_8a9e_24a09f20fefd_a2
-- name    : WilliamsonShmoys.planar_component_edge_extension__p2m_ae0a4a79_a73d_4cfa_8a9e_24a09f20fefd_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T22:36:17.883685+00:00
-- url     : https://prove2.me/theorems/5aa8d3b4-9880-40b3-8b69-bd7faf0454fe
-- title:
--   Extend a planar graph by an edge between unreachable vertices
-- statement:
--   Given a finite planar graph and distinct unreachable vertices, add the edge between them while retaining planarity. This is the geometric step: re-embed the components so the selected vertices are incident to exterior faces, then route an injective arc between them that avoids all other drawn edges. The new edge cannot already be present because its endpoints are unreachable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_component_edge_extension__p2m_ae0a4a79_a73d_4cfa_8a9e_24a09f20fefd_a2
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) {u v : V}
    (huv : u ≠ v) (hdis : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V, G ≤ H ∧ H.Adj u v ∧ HasPlanarDrawingOn H := by sorry
