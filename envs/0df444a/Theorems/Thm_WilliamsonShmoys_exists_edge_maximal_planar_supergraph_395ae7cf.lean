-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph_395ae7cf
-- name    : WilliamsonShmoys.exists_edge_maximal_planar_supergraph_395ae7cf
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T13:36:19.103295+00:00
-- url     : https://prove2.me/theorems/35c31141-898a-45cf-ad23-61c318b70e4e
-- title:
--   Planar edge-maximal supergraph
-- statement:
--   Every finite graph with a planar drawing has an inclusion-maximal planar supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_edge_maximal_planar_supergraph_395ae7cf
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ WilliamsonShmoys.HasPlanarDrawingOn G ∧
      ∀ J : SimpleGraph V, G ≤ J →
        WilliamsonShmoys.HasPlanarDrawingOn J → J = G := by sorry
