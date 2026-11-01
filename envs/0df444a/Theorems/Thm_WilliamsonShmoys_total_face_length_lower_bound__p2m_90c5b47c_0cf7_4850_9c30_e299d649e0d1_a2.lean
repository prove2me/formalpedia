-- Prove2me | Theorems.Thm_WilliamsonShmoys_total_face_length_lower_bound__p2m_90c5b47c_0cf7_4850_9c30_e299d649e0d1_a2
-- name    : WilliamsonShmoys.total_face_length_lower_bound__p2m_90c5b47c_0cf7_4850_9c30_e299d649e0d1_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:48:41.764381+00:00
-- url     : https://prove2.me/theorems/7ba1d8bc-08b7-409c-b8f6-c0f5fadf360e
-- title:
--   Lower bound the total facial walk length
-- statement:
--   If every list in a finite family has length at least three, the flattened family has length at least three times the number of lists. This includes the empty family.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem WilliamsonShmoys.total_face_length_lower_bound__p2m_90c5b47c_0cf7_4850_9c30_e299d649e0d1_a2 {V : Type} (k : ℕ) (faces : Fin k → List (V × V)) (hlen : ∀ i, 3 ≤ (faces i).length) : 3 * k ≤ (List.flatten (List.ofFn faces)).length := by sorry
