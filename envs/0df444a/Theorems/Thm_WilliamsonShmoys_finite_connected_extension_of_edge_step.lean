-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_connected_extension_of_edge_step
-- name    : WilliamsonShmoys.finite_connected_extension_of_edge_step
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T09:31:56.572431+00:00
-- url     : https://prove2.me/theorems/ca7bb854-915e-4ffa-b259-d02c594d3304
-- title:
--   Finite connected extension from a component-joining step
-- statement:
--   For a finite vertex type, if every disconnected extension satisfying a property can be further extended while preserving that property by an edge joining previously unreachable vertices, then there is a connected extension satisfying the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_connected_extension_of_edge_step
    {V : Type} [Fintype V]
    (T : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P T)
    (hStep : ∀ G : SimpleGraph V, T ≤ G → P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧
        ∃ u v : V, ¬ G.Reachable u v ∧ H.Adj u v) :
    ∃ S : SimpleGraph V, T ≤ S ∧ P S ∧ S.Connected := by sorry
