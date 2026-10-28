-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_connected_supergraph_of_edge_step
-- name    : WilliamsonShmoys.exists_connected_supergraph_of_edge_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T03:14:01.03706+00:00
-- url     : https://prove2.me/theorems/e651545f-b6b1-4128-bb0e-e1ed4f5a0739
-- title:
--   Finite iteration of component-joining extensions
-- statement:
--   If a property-preserving supergraph extension can always add an edge between vertices that were previously in different connected components, finitely many such extensions yield a connected supergraph with the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_connected_supergraph_of_edge_step
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V)
    (hH : P H)
    (hstep : ∀ G : SimpleGraph V, H ≤ G → P G → ¬ G.Connected →
      ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ K.Adj u v) :
    ∃ K : SimpleGraph V, H ≤ K ∧ K.Connected ∧ P K := by sorry
