-- Prove2me | Theorems.Thm_WilliamsonShmoys_treewidth_of_equiv_hom
-- name    : WilliamsonShmoys.treewidth_of_equiv_hom
-- status  : Proved
-- author  : @もち
-- created : 2026-11-25T08:09:01.764804+00:00
-- url     : https://prove2.me/theorems/8866924f-8ea3-4409-9a89-c584041bbdf0
-- title:
--   Tree-width is monotone under bijective homomorphic relabelling
-- statement:
--   Tree-width does not increase when the vertex set is relabelled by a bijection and edges are possibly removed.
--
--   Let $G$ be a graph on $V$, let $G'$ be a graph on $V'$, and let $e:V\to V'$ be a bijection such that every edge $ab$ of $G'$ comes from an edge $e^{-1}(a)\,e^{-1}(b)$ of $G$, so that $e^{-1}$ is a homomorphism $G'\to G$. Then
--
--   $$\mathrm{tw}(G)\le w\ \Longrightarrow\ \mathrm{tw}(G')\le w .$$
--
--   In particular tree-width is invariant under graph isomorphism. In Baker's technique this transports the tree-width bound for the disjoint union of the masked graphs, indexed by $\{0,\dots,k-1\}\times\{0,\dots,n-1\}$, to the same graph on $\{0,\dots,kn-1\}$, which is the form in which the subroutine solver is called.
--
--   **Formalization Note.** `TreewidthLE` is from `Def_RobertsonSeymour1986_GM5_TreewidthLE`, the existence of a tree-decomposition with all bags of size $\le w+1$.
-- source:
--   Robertson–Seymour, Graph Minors V (1986), Sect. 1 (definition of tree-width); used in Williamson–Shmoys Sect. 10.2

import Mathlib
import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

set_option autoImplicit false

theorem WilliamsonShmoys.treewidth_of_equiv_hom {V V' : Type} [DecidableEq V] [DecidableEq V']
    (G : SimpleGraph V) (G' : SimpleGraph V') (e : V ≃ V') (w : ℕ)
    (hadj : ∀ a b, G'.Adj a b → G.Adj (e.symm a) (e.symm b))
    (h : RobertsonSeymour1986.GM5.TreewidthLE G w) : RobertsonSeymour1986.GM5.TreewidthLE G' w := by sorry
