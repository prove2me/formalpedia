-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulating_planar_supergraph__p2m_64a468bf_7449_4dff_8ab0_8bb8c0a06a4e_a1
-- name    : WilliamsonShmoys.exists_triangulating_planar_supergraph__p2m_64a468bf_7449_4dff_8ab0_8bb8c0a06a4e_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T20:35:32.772128+00:00
-- url     : https://prove2.me/theorems/75824a43-ec60-475e-8ac2-3cc459e11047
-- title:
--   Augment a connected planar graph to a triangulation
-- statement:
--   A connected finite simple graph with at least three vertices and a crossing-free drawing can be augmented, without adding vertices, to a drawn simple graph containing all its edges and having exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.exists_triangulating_planar_supergraph__p2m_64a468bf_7449_4dff_8ab0_8bb8c0a06a4e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hV : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G.edgeSet ⊆ H.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  sorry
