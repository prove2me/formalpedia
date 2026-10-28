-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_planar_edge_extension_for_pair
-- name    : WilliamsonShmoys.exists_planar_edge_extension_for_pair
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-26T03:23:05.355973+00:00
-- url     : https://prove2.me/theorems/402aa87a-d0b9-47b0-93c9-98e38b99a8f6
-- title:
--   Planar extension for a prescribed unreachable pair
-- statement:
--   Given a crossing-free drawing of a graph and two vertices in different components, there is a planar supergraph containing the edge between those specified vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_planar_edge_extension_for_pair
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V)
    (hUV : ¬ G.Reachable u v) :
    ∃ K : SimpleGraph V, G ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧ K.Adj u v := by sorry
