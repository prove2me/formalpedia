-- Prove2me | Theorems.Thm_WilliamsonShmoys_retained_level_band
-- name    : WilliamsonShmoys.retained_level_band
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T21:24:36.200209+00:00
-- url     : https://prove2.me/theorems/9b4804db-29ca-4dd1-872f-0515cb31fbce
-- title:
--   A retained component lies within one short BFS-level interval
-- statement:
--   Every vertex in v's retained induced-graph component has BFS level in one shared interval of width less than k. A proof can induct along retained paths: adjacent BFS levels differ by at most one, and avoiding the residue j prevents a path from crossing a deleted level into another retained band. The interval argument handles k = 1 vacuously because no retained vertex can exist then.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_BakerLevel
import Mathlib.Combinatorics.SimpleGraph.Metric
set_option autoImplicit false

theorem WilliamsonShmoys.retained_level_band {n : Nat} (G : SimpleGraph (Fin n)) (k j : Nat) (hk : 0 < k) (hj : j < k) (v : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j}) : ∃ lo hi : Nat, hi - lo < k ∧ ∀ u : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j}, (G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).Reachable u v → lo ≤ WilliamsonShmoys.bakerLevel G u.1 ∧ WilliamsonShmoys.bakerLevel G u.1 ≤ hi := by sorry
