-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T06:25:10.295861+00:00
-- url     : https://prove2.me/theorems/26bed6b3-0e24-48f6-8bfc-300a5fad3823
-- title:
--   Finite maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite ordered vertex type has a drawable supergraph on the same vertices that is maximal among drawable supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_extension__p2m_ddfe16f2_466b_4eda_98ed_20e5107df448_a1 {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V) (hDraw : HasPlanarDrawingOn R) : ∃ T : SimpleGraph V, R ≤ T ∧ HasPlanarDrawingOn T ∧ ∀ N : SimpleGraph V, T ≤ N → HasPlanarDrawingOn N → N ≤ T := by sorry
