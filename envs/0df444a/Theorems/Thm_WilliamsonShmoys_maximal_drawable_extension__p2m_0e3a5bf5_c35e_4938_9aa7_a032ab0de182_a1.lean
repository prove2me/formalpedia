-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_drawable_extension__p2m_0e3a5bf5_c35e_4938_9aa7_a032ab0de182_a1
-- name    : WilliamsonShmoys.maximal_drawable_extension__p2m_0e3a5bf5_c35e_4938_9aa7_a032ab0de182_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:19:25.324476+00:00
-- url     : https://prove2.me/theorems/39578764-0198-4707-9e11-eef0219b5111
-- title:
--   Maximal drawable supergraph extension
-- statement:
--   Every drawable graph on a finite ordered vertex type is contained in a drawable graph maximal under graph inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_drawable_extension__p2m_0e3a5bf5_c35e_4938_9aa7_a032ab0de182_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      K ≤ L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
        ∀ M : SimpleGraph V, L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L := by sorry
