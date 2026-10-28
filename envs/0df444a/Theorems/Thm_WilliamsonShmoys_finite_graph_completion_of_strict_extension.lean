-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_completion_of_strict_extension
-- name    : WilliamsonShmoys.finite_graph_completion_of_strict_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:59:36.977543+00:00
-- url     : https://prove2.me/theorems/074d67a3-6957-4699-9ce3-33cc3af083e0
-- title:
--   Iterate strict extensions to reach a connected graph
-- statement:
--   For a finite vertex type, if every disconnected graph satisfying a property has a strictly larger-edge supergraph satisfying the same property, then every graph satisfying the property has a connected supergraph satisfying it and having at least as many edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_graph_completion_of_strict_extension
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hstep : ∀ (G : SimpleGraph V), P G → ¬ G.Connected →
      ∃ H : SimpleGraph V,
        G ≤ H ∧ G.edgeSet.ncard < H.edgeSet.ncard ∧ P H)
    (R : SimpleGraph V)
    (hR : P R) :
    ∃ S : SimpleGraph V,
      R.edgeSet.ncard ≤ S.edgeSet.ncard ∧
      S.Connected ∧ P S := by
  sorry
