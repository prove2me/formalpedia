-- Prove2me | Theorems.Thm_WilliamsonShmoys_retained_component_treewidth_of_bfs_bands
-- name    : WilliamsonShmoys.retained_component_treewidth_of_bfs_bands
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T21:11:24.399672+00:00
-- url     : https://prove2.me/theorems/fe0ba852-be99-476e-ae40-c991e5773e06
-- title:
--   Reduce retained components to BFS bands
-- statement:
--   If every reachable BFS band of fewer than k levels has treewidth at most 3k, then each component left after deleting levels congruent to j modulo k has treewidth at most 3k. The hypotheses retain the positive-k and strict residue-range conditions, including the vacuous k = 1 case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

theorem WilliamsonShmoys.retained_component_treewidth_of_bfs_bands {n : Nat} (G : SimpleGraph (Fin n)) (k j : Nat) (hk : 0 < k) (hj : j < k) (hBands : ∀ (root : Fin n) (lo hi : Nat), hi - lo < k → RobertsonSeymour1986.GM5.TreewidthLE (G.induce {x : Fin n | G.Reachable root x ∧ lo ≤ G.dist root x ∧ G.dist root x ≤ hi}) (3 * k)) : ∀ v : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j}, RobertsonSeymour1986.GM5.TreewidthLE (((G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).induce {u : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j} | (G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).Reachable u v})) (3 * k) := by sorry
