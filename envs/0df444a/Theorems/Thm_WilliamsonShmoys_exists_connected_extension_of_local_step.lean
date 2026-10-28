-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_extension_of_local_step
-- name    : WilliamsonShmoys.exists_connected_extension_of_local_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T22:50:20.169276+00:00
-- url     : https://prove2.me/theorems/4d5d87cc-42eb-4c29-a5ab-dda28bd436a0
-- title:
--   Finite maximal extension from local edge additions
-- statement:
--   For a finite vertex type, if every disconnected graph satisfying a property can be extended while preserving the property by adding at least one new edge, then every graph satisfying the property has a connected supergraph satisfying it. Prove this by choosing a maximal qualifying supergraph among the finitely many graphs containing the input.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_connected_extension_of_local_step
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (hStep : ∀ K : SimpleGraph V, P K → ¬ K.Connected →
      ∃ L : SimpleGraph V, K ≤ L ∧ P L ∧
        ∃ u v : V, L.Adj u v ∧ ¬ K.Adj u v)
    (H : SimpleGraph V) (hP : P H) :
    ∃ G : SimpleGraph V, H ≤ G ∧ P G ∧ G.Connected := by sorry
