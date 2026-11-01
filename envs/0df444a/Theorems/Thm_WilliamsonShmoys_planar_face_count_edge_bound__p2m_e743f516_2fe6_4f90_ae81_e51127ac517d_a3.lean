-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_face_count_edge_bound__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a3
-- name    : WilliamsonShmoys.planar_face_count_edge_bound__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:52:45.945573+00:00
-- url     : https://prove2.me/theorems/74472c09-fcc2-4630-ae8d-0fcadf6a2324
-- title:
--   Edge bound from face counts
-- statement:
--   Derive the planar edge bound from face lengths of at least three, the two-sides-per-edge count, and Euler's relation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

theorem WilliamsonShmoys.planar_face_count_edge_bound__p2m_e743f516_2fe6_4f90_ae81_e51127ac517d_a3 (v e : Nat) (lengths : List Nat) (hcard : Nat.le 3 v) (hlength : forall l : Nat, List.Mem l lengths -> Nat.le 3 l) (hsides : lengths.sum = 2 * e) (heuler : v + lengths.length = e + 2) : Nat.le (e + 6) (3 * v) := by sorry
