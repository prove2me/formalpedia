-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_maximal_completion__p2m_e3eb1401_8114_44d9_870e_95a93988f448_a1
-- name    : WilliamsonShmoys.planar_triangulation_maximal_completion__p2m_e3eb1401_8114_44d9_870e_95a93988f448_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T15:25:59.848916+00:00
-- url     : https://prove2.me/theorems/e6ecd03e-0848-4570-b64b-bef34c00a76f
-- title:
--   Finite maximal planar supergraph completion
-- statement:
--   Every drawable graph on a finite linearly ordered vertex type has a drawable supergraph on the same vertex type that contains all its edges and is maximal under edge inclusion among drawable graphs. The n ≥ 3 hypothesis is retained to match the parent, though finite maximality itself does not need it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_triangulation_maximal_completion__p2m_e3eb1401_8114_44d9_870e_95a93988f448_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : HasPlanarDrawingOn G) :
    ∃ L : SimpleGraph V,
      HasPlanarDrawingOn L ∧
      (∀ u v, G.Adj u v → L.Adj u v) ∧
      (∀ M : SimpleGraph V, HasPlanarDrawingOn M →
        (∀ u v, L.Adj u v → M.Adj u v) →
        ∀ u v, M.Adj u v → L.Adj u v) := by sorry
