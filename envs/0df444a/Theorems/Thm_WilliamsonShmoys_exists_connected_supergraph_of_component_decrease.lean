-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_component_decrease
-- name    : WilliamsonShmoys.exists_connected_supergraph_of_component_decrease
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:21:27.792977+00:00
-- url     : https://prove2.me/theorems/b908f551-8ff3-4068-92c0-8421a88a8574
-- title:
--   Finite iteration of strict component decreases
-- statement:
--   If every disconnected property-preserving supergraph has a further property-preserving extension with strictly fewer connected components, then some such extension of H is connected.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_connected_supergraph_of_component_decrease
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hH : P H)
    (hstep : ∀ G : SimpleGraph V, H ≤ G → P G → ¬ G.Connected →
      ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧
        Nat.card K.ConnectedComponent < Nat.card G.ConnectedComponent) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ P K := by sorry
