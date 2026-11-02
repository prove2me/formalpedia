-- Prove2me | Theorems.Thm_WilliamsonShmoys_planarDrawingOn_maximalExtension__p2m_bc222e64_5fd0_4544_bad9_127a7d6f7d68_a2
-- name    : WilliamsonShmoys.planarDrawingOn_maximalExtension__p2m_bc222e64_5fd0_4544_bad9_127a7d6f7d68_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:00:20.997216+00:00
-- url     : https://prove2.me/theorems/1e3a6908-3e59-4565-92f0-171f972a39c8
-- title:
--   Extend a drawable graph to a maximal drawable graph
-- statement:
--   A graph drawable on a finite ordered vertex type has a maximal drawable supergraph on that same vertex type. Choose a drawable supergraph with the largest possible finite edge set; any drawable supergraph of it must have the same edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planarDrawingOn_maximalExtension__p2m_bc222e64_5fd0_4544_bad9_127a7d6f7d68_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ K' : SimpleGraph V, K ≤ K' → HasPlanarDrawingOn K' → K' = K := by sorry
