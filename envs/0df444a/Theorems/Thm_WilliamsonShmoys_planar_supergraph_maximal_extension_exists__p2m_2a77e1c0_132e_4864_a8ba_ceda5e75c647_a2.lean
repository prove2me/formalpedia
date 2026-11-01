-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal_extension_exists__p2m_2a77e1c0_132e_4864_a8ba_ceda5e75c647_a2
-- name    : WilliamsonShmoys.planar_supergraph_maximal_extension_exists__p2m_2a77e1c0_132e_4864_a8ba_ceda5e75c647_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T03:12:57.17607+00:00
-- url     : https://prove2.me/theorems/bb3435ff-6572-4e78-a151-259180a5e146
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every finite connected graph with a crossing-free drawing has an inclusion-maximal planar supergraph on the same vertex type. The extension remains connected and has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_supergraph_maximal_extension_exists__p2m_2a77e1c0_132e_4864_a8ba_ceda5e75c647_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn G)
    (hconn : G.Connected) :
    Exists fun H : SimpleGraph V =>
      G <= H /\
      HasPlanarDrawingOn H /\
      G.edgeSet.ncard <= H.edgeSet.ncard /\
      H.Connected /\
      (forall K : SimpleGraph V, H <= K -> HasPlanarDrawingOn K -> K = H) := by sorry
