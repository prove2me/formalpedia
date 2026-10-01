-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_bfs_band_treewidth
-- name    : WilliamsonShmoys.planar_bfs_band_treewidth
-- status  : Open
-- author  : @Gabewhigham
-- created : 2026-09-30T13:51:57.962705+00:00
-- url     : https://prove2.me/theorems/f8e44dd0-91d4-479e-999f-a811c044d56a
-- title:
--   Deleting every $k$-th BFS level of a planar graph leaves tree-width at most $3k$
-- statement:
--   Let $G$ be a simple graph on $\{0,\dots,n-1\}$ that has a crossing-free drawing in the plane (`HasPlanarDrawing G`). Run breadth-first search from the least vertex of each connected component and let $\ell(v)$ be the resulting level of $v$ (`bakerLevel G v`). Fix $k\ge1$ and $0\le j<k$, and delete every vertex whose level is congruent to $j$ modulo $k$. Then the remaining induced subgraph
--
--   $$G_j = G\bigl[\{v : \ell(v) \not\equiv j \pmod k\}\bigr]$$
--
--   has tree-width at most $3k$.
--
--   This is the structural half of Baker's technique (Williamson–Shmoys, proof of Theorem 10.11): each connected piece of $G_j$ lies within fewer than $k$ consecutive BFS levels; contracting all lower levels to a single vertex yields a planar graph of radius less than $k$, whose tree-width is $O(k)$ (a planar graph of radius $r$ has tree-width at most $3r+1$). The bound $3k$ is chosen with slack.
--
--   **Formalization note.** Tree-width is `RobertsonSeymour1986.GM5.TreewidthLE` (existence of a tree-decomposition with bags of size at most $3k+1$), applied to the induced subgraph `G.induce`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarIndependentSetRAM
import Definitions.Def_WilliamsonShmoys_BakerLevel
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

namespace WilliamsonShmoys
theorem planar_bfs_band_treewidth {n : ℕ} (G : SimpleGraph (Fin n)) (k j : ℕ)
    (hk : 0 < k) (hj : j < k) (hG : HasPlanarDrawing G) :
    RobertsonSeymour1986.GM5.TreewidthLE
      (G.induce {v : Fin n | bakerLevel G v % k ≠ j}) (3 * k) := by sorry
end WilliamsonShmoys
