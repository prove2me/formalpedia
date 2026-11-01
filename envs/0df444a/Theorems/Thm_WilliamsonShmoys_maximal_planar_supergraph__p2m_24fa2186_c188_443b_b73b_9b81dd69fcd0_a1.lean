-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_24fa2186_c188_443b_b73b_9b81dd69fcd0_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_24fa2186_c188_443b_b73b_9b81dd69fcd0_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:14:53.328345+00:00
-- url     : https://prove2.me/theorems/dadb618c-bc75-460f-8f06-1e80a6623732
-- title:
--   Existence of an inclusion-maximal planar supergraph
-- statement:
--   Every finite connected graph with a crossing-free drawing and at least three vertices has a planar supergraph on the same vertices that has no strictly larger planar supergraph on that vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_24fa2186_c188_443b_b73b_9b81dd69fcd0_a1
    {U : Type} [Fintype U] [LinearOrder U]
    (G : SimpleGraph U) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hconn : G.Connected) (hcard : 3 ≤ Fintype.card U) :
    ∃ H : SimpleGraph U, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph U, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
