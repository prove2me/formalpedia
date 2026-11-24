-- Prove2me | Theorems.Thm_WilliamsonShmoys_treewidth_masked_of_induced
-- name    : WilliamsonShmoys.treewidth_masked_of_induced
-- status  : Proved
-- author  : @もち
-- created : 2026-11-24T05:55:27.609916+00:00
-- url     : https://prove2.me/theorems/e5fef8d9-3862-4924-b12b-d89a60bb7133
-- title:
--   Masking edges outside an induced subgraph preserves tree-width
-- statement:
--   Let $G$ be a simple graph on $\{0,\dots,n-1\}$, let $P$ be a predicate on vertices, and let $S=\{v : P(v)\}$. Write $G_P$ for the graph on **all** $n$ vertices whose edges are the edges of $G$ with both ends in $S$; the vertices outside $S$ become isolated. If the induced subgraph $G[S]$ has tree-width at most $w$, then
--
--   $$\operatorname{tw}(G_P)\le w.$$
--
--   This lemma lets an algorithm that needs the tree-width of its whole input graph run on $G[S]$ by masking edges, without renumbering vertices. In Baker's shifting technique it turns a tree-width bound for the graph with one BFS level class removed into a bound for the masked instance on the same vertex set.
--
--   **Formalization Note.** $G_P$ is `SimpleGraph.fromRel (fun u v => G.Adj u v ∧ P u ∧ P v)`, and tree-width is `RobertsonSeymour1986.GM5.TreewidthLE`.
-- source:
--   Robertson–Seymour, Graph Minors V (1986), Sect. 1 (tree-decompositions); used for Baker's technique in Williamson–Shmoys, The Design of Approximation Algorithms, Sect. 10.2, pp. 270–271

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

theorem WilliamsonShmoys.treewidth_masked_of_induced
    {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) (w : ℕ)
    (h : RobertsonSeymour1986.GM5.TreewidthLE (G.induce {v | P v}) w) :
    RobertsonSeymour1986.GM5.TreewidthLE
      (SimpleGraph.fromRel (fun u v => G.Adj u v ∧ P u ∧ P v)) w := by sorry
