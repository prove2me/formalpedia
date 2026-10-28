-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_baker_band_treewidth
-- name    : WilliamsonShmoys.planar_baker_band_treewidth
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T20:42:58.316985+00:00
-- url     : https://prove2.me/theorems/2f886b93-4e07-4094-a9e1-25cea2d69341
-- title:
--   Treewidth bound for a connected component of a retained BFS band
-- statement:
--   For every vertex in the graph left after deleting BFS levels congruent to j modulo k, the connected component containing it has treewidth at most 3k. The strict range 0 ≤ j < k and positivity of k are retained. When k = 1 there are no such vertices, so the claim is vacuous.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

theorem WilliamsonShmoys.planar_baker_band_treewidth {n : ℕ} (G : SimpleGraph (Fin n)) (k j : ℕ) (hk : 0 < k) (hj : j < k) (hG : WilliamsonShmoys.HasPlanarDrawing G) : ∀ v : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j}, RobertsonSeymour1986.GM5.TreewidthLE (((G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).induce {u : {x : Fin n // WilliamsonShmoys.bakerLevel G x % k ≠ j} | (G.induce {x : Fin n | WilliamsonShmoys.bakerLevel G x % k ≠ j}).Reachable u v})) (3 * k) := by sorry
