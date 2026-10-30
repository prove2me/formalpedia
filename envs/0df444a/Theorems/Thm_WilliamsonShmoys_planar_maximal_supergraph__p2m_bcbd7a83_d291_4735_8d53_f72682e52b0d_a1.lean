-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_bcbd7a83_d291_4735_8d53_f72682e52b0d_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph__p2m_bcbd7a83_d291_4735_8d53_f72682e52b0d_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T04:35:19.734578+00:00
-- url     : https://prove2.me/theorems/6a3d0978-a2a8-418a-a56b-10e4c543dafd
-- title:
--   Planar edge-maximal supergraph on the same vertices
-- statement:
--   Any graph with the given planar drawing and at least three vertices has a planar supergraph on the same vertices that admits no proper planar supergraph on those vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_maximal_supergraph__p2m_bcbd7a83_d291_4735_8d53_f72682e52b0d_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      M ≤ N ∧ HasPlanarDrawingOn N ∧
      ∀ K : SimpleGraph V, N ≤ K → HasPlanarDrawingOn K → K = N := by sorry
