-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_face_count_identities__p2m_24cd5df2_f06e_484a_a9e0_671b5163ec2a_a1
-- name    : WilliamsonShmoys.maximal_planar_face_count_identities__p2m_24cd5df2_f06e_484a_a9e0_671b5163ec2a_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:29:50.609196+00:00
-- url     : https://prove2.me/theorems/2c52a5e8-a177-4eaa-adc1-eeae3ac4d632
-- title:
--   Face-count identities for maximal planar drawings
-- statement:
--   For a maximal planar graph on at least three vertices, there is a face count f such that each face contributes three edge incidences and Euler’s formula holds: twice the edge count is three times f, and vertices plus faces equal edges plus two.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_face_count_identities__p2m_24cd5df2_f06e_484a_a9e0_671b5163ec2a_a1 {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V) (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) (hcard : 3 <= Fintype.card V) (hmax : forall M' : SimpleGraph V, M <= M' -> WilliamsonShmoys.HasPlanarDrawingOn M' -> M' = M) : ∃ f : ℕ, 2 * M.edgeSet.ncard = 3 * f ∧ Fintype.card V + f = M.edgeSet.ncard + 2 := by sorry
