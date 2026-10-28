-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_bfs_annulus_treewidth
-- name    : WilliamsonShmoys.planar_bfs_annulus_treewidth
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-25T21:10:57.272926+00:00
-- url     : https://prove2.me/theorems/0bceffec-a475-4e7e-b20e-8fc786a298cc
-- title:
--   Treewidth bound for a planar BFS annulus
-- statement:
--   For a graph with the given planar drawing, the subgraph induced by vertices reachable from a root and with distances in an interval of width less than k has treewidth at most 3k. If the interval is empty, the induced graph is empty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

theorem WilliamsonShmoys.planar_bfs_annulus_treewidth {n : Nat} (G : SimpleGraph (Fin n)) (root : Fin n) (k : Nat) (lo hi : Nat) (hwidth : hi - lo < k) (hG : WilliamsonShmoys.HasPlanarDrawing G) : RobertsonSeymour1986.GM5.TreewidthLE (G.induce {x : Fin n | G.Reachable root x ∧ lo ≤ G.dist root x ∧ G.dist root x ≤ hi}) (3 * k) := by sorry
