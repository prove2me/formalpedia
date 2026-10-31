-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_dc87cfcb_d23b_4346_97a4_7d4d545de3b6_a1
-- name    : WilliamsonShmoys.maximal_planar_extension__p2m_dc87cfcb_d23b_4346_97a4_7d4d545de3b6_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T09:29:37.949934+00:00
-- url     : https://prove2.me/theorems/a874f652-e0a4-4d47-9ec5-8884fbe44a1d
-- title:
--   Maximal planar extension on a fixed vertex set
-- statement:
--   Every graph with a drawing as defined in the supplied module is contained in an inclusion-maximal graph with such a drawing on the same finite vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false
open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_extension__p2m_dc87cfcb_d23b_4346_97a4_7d4d545de3b6_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) : ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧ ∀ G : SimpleGraph V, HasPlanarDrawingOn G → H ≤ G → G ≤ H := by sorry
