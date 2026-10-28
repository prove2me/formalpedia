-- Prove2me | Theorems.Thm_WilliamsonShmoys_treewidthLE_of_graph_embedding
-- name    : WilliamsonShmoys.treewidthLE_of_graph_embedding
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T21:36:58.502216+00:00
-- url     : https://prove2.me/theorems/3f68606c-fd93-42b4-8e3c-b928ece21817
-- title:
--   Treewidth is preserved under injective graph embeddings
-- statement:
--   An injective map that preserves and reflects adjacency transfers any treewidth upper bound from the larger graph to the embedded graph, by pulling back the bags of a finite tree decomposition.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

theorem WilliamsonShmoys.treewidthLE_of_graph_embedding {α β : Type} [DecidableEq α] [DecidableEq β] (K : SimpleGraph α) (H : SimpleGraph β) (f : α → β) (w : Nat) (hinj : Function.Injective f) (hadj : ∀ x y, K.Adj x y ↔ H.Adj (f x) (f y)) : RobertsonSeymour1986.GM5.TreewidthLE H w → RobertsonSeymour1986.GM5.TreewidthLE K w := by sorry
