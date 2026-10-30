-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension__p2m_3662a54d_ea7a_4ea3_804a_c2f8a32e2408_a1
-- name    : WilliamsonShmoys.planar_maximal_extension__p2m_3662a54d_ea7a_4ea3_804a_c2f8a32e2408_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:46:24.92124+00:00
-- url     : https://prove2.me/theorems/3b1294a1-b2ad-4848-a1e5-70cdfc894c2b
-- title:
--   Maximal planar extension on a fixed vertex type
-- statement:
--   Every finite connected graph with a crossing-free drawing and at least three vertices is contained in an inclusion-maximal graph on the same vertex type that still has a crossing-free drawing; the extension remains connected and has at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_extension__p2m_3662a54d_ea7a_4ea3_804a_c2f8a32e2408_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      H.Connected ∧
      (∀ K : SimpleGraph V,
        H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  sorry
