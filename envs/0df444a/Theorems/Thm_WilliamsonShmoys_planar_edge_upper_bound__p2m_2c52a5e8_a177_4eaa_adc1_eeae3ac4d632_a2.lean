-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_2c52a5e8_a177_4eaa_adc1_eeae3ac4d632_a2
-- name    : WilliamsonShmoys.planar_edge_upper_bound__p2m_2c52a5e8_a177_4eaa_adc1_eeae3ac4d632_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:41:19.781199+00:00
-- url     : https://prove2.me/theorems/a5e7ae3f-df22-45e2-9fd6-19c86751b0d6
-- title:
--   Planar edge upper bound
-- statement:
--   Every finite simple planar graph with at least three vertices has at most 3n−6 edges. The subtraction-free conclusion retains the exact range needed by the target.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_upper_bound__p2m_2c52a5e8_a177_4eaa_adc1_eeae3ac4d632_a2 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) : M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by sorry
