-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_5852e9a6_6924_436b_b46b_8836657b1500_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5852e9a6_6924_436b_b46b_8836657b1500_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T19:02:11.652556+00:00
-- url     : https://prove2.me/theorems/3e90732e-198c-49e6-bc99-e20ae24f512c
-- title:
--   Existence of a maximal planar supergraph
-- statement:
--   Every planar graph on a finite linearly ordered vertex type has a planar supergraph on that same vertex type that has no strict planar supergraph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

/-- A finite planar graph has a maximal planar supergraph on the same vertex set. -/

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_5852e9a6_6924_436b_b46b_8836657b1500_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V, G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H := by sorry
