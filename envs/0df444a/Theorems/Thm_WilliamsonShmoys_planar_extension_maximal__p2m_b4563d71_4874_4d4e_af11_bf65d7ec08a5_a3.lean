-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_extension_maximal__p2m_b4563d71_4874_4d4e_af11_bf65d7ec08a5_a3
-- name    : WilliamsonShmoys.planar_extension_maximal__p2m_b4563d71_4874_4d4e_af11_bf65d7ec08a5_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T21:50:19.315352+00:00
-- url     : https://prove2.me/theorems/69d74bef-9aa8-40b9-8469-f44173b0c825
-- title:
--   Every finite drawable graph has a maximal drawable extension
-- statement:
--   Every finite graph with a planar drawing has a planar supergraph on the same vertices that has no strictly larger planar supergraph. Choose a drawable supergraph containing the input with the largest edge set among the finitely many simple graphs on those vertices. No lower bound on the number of vertices is needed.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_extension_maximal__p2m_b4563d71_4874_4d4e_af11_bf65d7ec08a5_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V,
          WilliamsonShmoys.HasPlanarDrawingOn M → L ≤ M → M = L := by sorry
