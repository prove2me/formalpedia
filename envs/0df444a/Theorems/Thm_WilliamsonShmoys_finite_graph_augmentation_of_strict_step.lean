-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_augmentation_of_strict_step
-- name    : WilliamsonShmoys.finite_graph_augmentation_of_strict_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T12:53:10.984987+00:00
-- url     : https://prove2.me/theorems/eee18f21-eea5-4475-bc4f-e03bc4fbc087
-- title:
--   Finite graph augmentation from strict extension steps
-- statement:
--   For a finite vertex type, if a graph property is preserved by a strict-supergraph step whenever a graph with that property is disconnected, then every graph with the property has a connected supergraph with the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_augmentation_of_strict_step
    {V : Type} [Fintype V] [LinearOrder V]
    (D : SimpleGraph V → Prop)
    (P : SimpleGraph V)
    (hP : D P)
    (hStep : ∀ G : SimpleGraph V, D G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G < H ∧ D H) :
    ∃ Q : SimpleGraph V, P ≤ Q ∧ Q.Connected ∧ D Q := by sorry
