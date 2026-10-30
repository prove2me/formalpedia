-- Prove2me | Theorems.Thm_WilliamsonShmoys_simpleGraph_finite_of_fintype__p2m_c9fc3f38_cd2a_4e85_9567_ad68f211d82b_a1
-- name    : WilliamsonShmoys.simpleGraph_finite_of_fintype__p2m_c9fc3f38_cd2a_4e85_9567_ad68f211d82b_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T00:41:12.745201+00:00
-- url     : https://prove2.me/theorems/a6c33541-30a5-4471-bb37-90fe60990853
-- title:
--   Simple graphs on a finite vertex type form a finite type
-- statement:
--   For a finite vertex type, there are only finitely many simple graphs on that type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.simpleGraph_finite_of_fintype__p2m_c9fc3f38_cd2a_4e85_9567_ad68f211d82b_a1 {V : Type} [Fintype V] : Finite (SimpleGraph V) := by sorry
