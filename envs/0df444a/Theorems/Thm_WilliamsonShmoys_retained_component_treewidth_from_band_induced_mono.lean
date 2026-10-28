-- Prove2me | Theorems.Thm_WilliamsonShmoys_retained_component_treewidth_from_band_induced_mono
-- name    : WilliamsonShmoys.retained_component_treewidth_from_band_induced_mono
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-25T21:24:19.505084+00:00
-- url     : https://prove2.me/theorems/91e5d754-ca89-44e2-b217-e5bbae9265b9
-- title:
--   Treewidth is inherited by nested induced subgraphs
-- statement:
--   If every vertex selected by Q inside R also belongs to B, then the graph induced by Q inside the graph induced by R inherits the treewidth bound of the graph induced by B.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_RobertsonSeymour1986_GM5_TreewidthLE

theorem WilliamsonShmoys.retained_component_treewidth_from_band_induced_mono {V : Type} [DecidableEq V] (G : SimpleGraph V) (R B : Set V) (Q : {x : V // x ∈ R} → Prop) (hQB : ∀ x : {x : V // x ∈ R}, Q x → (x : V) ∈ B) (w : Nat) : RobertsonSeymour1986.GM5.TreewidthLE (G.induce B) w → RobertsonSeymour1986.GM5.TreewidthLE ((G.induce R).induce Q) w := by sorry
