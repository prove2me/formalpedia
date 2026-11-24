-- Prove2me | Theorems.Thm_WilliamsonShmoys_treewidth_disjoint_union_le
-- name    : WilliamsonShmoys.treewidth_disjoint_union_le
-- status  : Open
-- author  : @もち
-- created : 2026-11-24T10:44:55.687712+00:00
-- url     : https://prove2.me/theorems/5f42d7c8-ca87-4644-9b52-e22ef3844c24
-- title:
--   Tree-width of a disjoint union is at most the maximum
-- statement:
--   Let $H_0,\dots,H_{m-1}$ be simple graphs on the vertex set $\{0,\dots,n-1\}$, each of tree-width at most $w$. Let $U$ be their disjoint union on the vertex set $\{0,\dots,m-1\}\times\{0,\dots,n-1\}$: two vertices $(j,a)$ and $(j',b)$ are adjacent exactly when $j=j'$ and $a,b$ are adjacent in $H_j$. Then
--
--   $$\operatorname{tw}(U)\le w.$$
--
--   This lets a single call of an exact tree-width solver handle $m$ instances at once. In the RAM implementation of Baker's shifting technique, the $k$ masked instances are combined into one disjoint union, so that the solver runs once from a clean initial memory.
--
--   **Formalization Note.** $U$ is `SimpleGraph.fromRel (fun u v => u.1 = v.1 ∧ (H u.1).Adj u.2 v.2)` on `Fin m × Fin n`; tree-width is `RobertsonSeymour1986.GM5.TreewidthLE`. The case $m=0$ (no vertices) is included.
-- source:
--   Robertson–Seymour, Graph Minors V (1986), Sect. 1 (tree-decompositions); used for the RAM implementation of Williamson–Shmoys, Sect. 10.2

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

theorem WilliamsonShmoys.treewidth_disjoint_union_le {m n : ℕ} (H : Fin m → SimpleGraph (Fin n)) (w : ℕ)
    (h : ∀ j, RobertsonSeymour1986.GM5.TreewidthLE (H j) w) :
    RobertsonSeymour1986.GM5.TreewidthLE
      (SimpleGraph.fromRel (fun (u v : Fin m × Fin n) => u.1 = v.1 ∧ (H u.1).Adj u.2 v.2)) w := by sorry
