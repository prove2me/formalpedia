-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_finite_step_completion__p2m_3b9c1b25_36f2_49fb_9760_e5ee7be0caf4_a1
-- name    : WilliamsonShmoys.planar_finite_step_completion__p2m_3b9c1b25_36f2_49fb_9760_e5ee7be0caf4_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:49:12.253732+00:00
-- url     : https://prove2.me/theorems/a9a5aac4-cf42-46e5-abca-ec8765edbc1f
-- title:
--   Iterate finite planar-preserving edge extensions to connectivity
-- statement:
--   For a finite linearly ordered vertex type, if a graph property permits adding an edge between any disconnected pair while preserving the property and all existing edges, then a graph with that property can be extended to a connected graph while retaining the original edges. The empty vertex type and already-connected graphs require no extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.planar_finite_step_completion__p2m_3b9c1b25_36f2_49fb_9760_e5ee7be0caf4_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (J : SimpleGraph V) (hJ : P J)
    (hstep : ∀ G : SimpleGraph V, P G →
      letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
        fun K => Classical.decRel K.Adj
      ∀ u v : V, ¬ Nonempty (G.Walk u v) →
        ∃ H : SimpleGraph V,
          P H ∧ G.edgeFinset ⊆ H.edgeFinset ∧ H.Adj u v) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ H : SimpleGraph V,
      P H ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      J.edgeFinset ⊆ H.edgeFinset := by sorry
