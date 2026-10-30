-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_exists__p2m_efe3e864_4fbd_4f0b_a1f2_70ba02623cb8_a1
-- name    : WilliamsonShmoys.planar_maximal_extension_exists__p2m_efe3e864_4fbd_4f0b_a1f2_70ba02623cb8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:08:42.223222+00:00
-- url     : https://prove2.me/theorems/c5685e49-0d83-46bc-bcc2-05a6dc60419f
-- title:
--   Existence of an inclusion-maximal drawable extension
-- statement:
--   Every finite graph with a crossing-free drawing has an inclusion-maximal drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_extension_exists__p2m_efe3e864_4fbd_4f0b_a1f2_70ba02623cb8_a1 {V : Type} [Fintype V] [LinearOrder V] (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) : ∃ K : SimpleGraph V, N ≤ K ∧ HasPlanarDrawingOn K ∧ ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
