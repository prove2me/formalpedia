-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_add_edge_between_components__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a1
-- name    : WilliamsonShmoys.planar_add_edge_between_components__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-29T20:18:07.769663+00:00
-- url     : https://prove2.me/theorems/4517a7f1-944d-422f-bf5b-d4e0c164a70b
-- title:
--   Planar graphs admit an edge between distinct components
-- statement:
--   Given a planar drawing and two distinct vertices in separate components, there is a planar strict supergraph on the same vertices that includes the edge between them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
open WilliamsonShmoys

theorem WilliamsonShmoys.planar_add_edge_between_components__p2m_293787da_4b73_4bb8_b4f9_49ac7bd93d8f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (u v : V)
    (hG : HasPlanarDrawingOn G)
    (huv : u ≠ v)
    (hnot : ¬ G.Reachable u v) :
    ∃ H : SimpleGraph V, G < H ∧ H.Adj u v ∧ HasPlanarDrawingOn H := by sorry
