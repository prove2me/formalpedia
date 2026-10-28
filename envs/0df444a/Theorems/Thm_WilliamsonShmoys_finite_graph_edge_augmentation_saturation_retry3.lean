-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_edge_augmentation_saturation_retry3
-- name    : WilliamsonShmoys.finite_graph_edge_augmentation_saturation_retry3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T01:47:22.549987+00:00
-- url     : https://prove2.me/theorems/9f6f2c83-e0fe-4411-bc80-625f8f286f7d
-- title:
--   Iterating bounded one-edge augmentations
-- statement:
--   For a property of finite graphs, if every graph with that property has at most M edges and each such graph below M can be extended by one edge while retaining the property, then any starting graph with the property extends to one with exactly M edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_edge_augmentation_saturation_retry3 {V : Type} [Fintype V] (P : SimpleGraph V -> Prop) (L : SimpleGraph V) (M : Nat) (hP : P L) (hBound : forall G : SimpleGraph V, P G -> G.edgeSet.ncard <= M) (hAugment : forall G : SimpleGraph V, P G -> G.edgeSet.ncard < M -> exists H : SimpleGraph V, G <= H /\ P H /\ H.edgeSet.ncard = G.edgeSet.ncard + 1) : exists K : SimpleGraph V, L <= K /\ P K /\ K.edgeSet.ncard = M := by sorry
