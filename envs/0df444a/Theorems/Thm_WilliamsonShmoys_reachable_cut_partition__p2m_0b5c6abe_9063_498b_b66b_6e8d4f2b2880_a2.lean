-- Prove2me | Theorems.Thm_WilliamsonShmoys_reachable_cut_partition__p2m_0b5c6abe_9063_498b_b66b_6e8d4f2b2880_a2
-- name    : WilliamsonShmoys.reachable_cut_partition__p2m_0b5c6abe_9063_498b_b66b_6e8d4f2b2880_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-31T20:57:56.224126+00:00
-- url     : https://prove2.me/theorems/911049cd-d408-4b23-b288-0798ce02f9ca
-- title:
--   Non-reachability yields an edge-free cut
-- statement:
--   The vertices reachable from `u` form a cut containing `u` and excluding `v`; no edge of `G` crosses this cut. The proof is by reachability closure: an edge crossing out of the reachable set would make its endpoint reachable. This removes the graph-theoretic partition step from the parent.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.reachable_cut_partition__p2m_0b5c6abe_9063_498b_b66b_6e8d4f2b2880_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (hsep : ¬ G.Reachable u v) :
    ∃ S : Set V, u ∈ S ∧ v ∉ S ∧
      ∀ ⦃a b : V⦄, a ∈ S → b ∉ S → ¬ G.Adj a b := by
  sorry
