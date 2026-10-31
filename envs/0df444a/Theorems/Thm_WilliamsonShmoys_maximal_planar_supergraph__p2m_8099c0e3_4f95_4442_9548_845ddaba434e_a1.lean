-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_8099c0e3_4f95_4442_9548_845ddaba434e_a1
-- name    : WilliamsonShmoys.maximal_planar_supergraph__p2m_8099c0e3_4f95_4442_9548_845ddaba434e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:17:07.002957+00:00
-- url     : https://prove2.me/theorems/98144ef0-c988-4b8f-aaba-1bdea0bce009
-- title:
--   Every finite planar graph has an edge-maximal planar supergraph on the same vertices
-- statement:
--   For a finite linearly ordered vertex type, every graph with a planar drawing has a planar supergraph on the same vertices that is maximal under planar graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_supergraph__p2m_8099c0e3_4f95_4442_9548_845ddaba434e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V, K ≤ L ∧ HasPlanarDrawingOn L ∧
      (∀ M : SimpleGraph V, L ≤ M → HasPlanarDrawingOn M → M = L) := by sorry
