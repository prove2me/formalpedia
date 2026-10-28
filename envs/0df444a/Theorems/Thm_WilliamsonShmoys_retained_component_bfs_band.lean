-- Prove2me | Theorems.Thm_WilliamsonShmoys_retained_component_bfs_band
-- name    : WilliamsonShmoys.retained_component_bfs_band
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T21:15:35.27001+00:00
-- url     : https://prove2.me/theorems/6c289057-d569-4deb-842a-84b33650b807
-- title:
--   A retained component lies in one BFS band
-- statement:
--   For a retained vertex v, all vertices in its retained induced-graph component are reachable from v’s canonical BFS root and have distances within some interval [lo, hi] with hi − lo < k. The proof should use that reachable vertices have the same canonical component root, adjacent vertices’ distances differ by at most one, and paths in the retained graph avoid every level congruent to j modulo k. In the k = 1 case there is no v, so the statement is vacuous.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_BakerLevel
import Mathlib.Combinatorics.SimpleGraph.Metric

set_option autoImplicit false

theorem WilliamsonShmoys.retained_component_bfs_band {n : Nat} (G : SimpleGraph (Fin n)) (k j : Nat) (hk : 0 < k) (hj : j < k) (v : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j}) : ∃ lo hi : Nat, hi - lo < k ∧ ∀ u : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j}, (G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).Reachable u v → G.Reachable (WilliamsonShmoys.bakerRoot G v.1) u.1 ∧ lo ≤ G.dist (WilliamsonShmoys.bakerRoot G v.1) u.1 ∧ G.dist (WilliamsonShmoys.bakerRoot G v.1) u.1 ≤ hi := by sorry
