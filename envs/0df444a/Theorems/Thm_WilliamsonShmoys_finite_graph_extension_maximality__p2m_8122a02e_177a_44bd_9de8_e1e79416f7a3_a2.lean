-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_extension_maximality__p2m_8122a02e_177a_44bd_9de8_e1e79416f7a3_a2
-- name    : WilliamsonShmoys.finite_graph_extension_maximality__p2m_8122a02e_177a_44bd_9de8_e1e79416f7a3_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:04:10.105292+00:00
-- url     : https://prove2.me/theorems/69ce2e0a-bca0-4126-a521-874397764f0e
-- title:
--   Finite maximality for graph extensions
-- statement:
--   For a finite vertex type, if a property holds for a starting graph and every disconnected graph with that property above the starting graph has a strictly larger extension with the property, then there is a connected extension with the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.finite_graph_extension_maximality__p2m_8122a02e_177a_44bd_9de8_e1e79416f7a3_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hP : P N)
    (hstep : ∀ M : SimpleGraph V, N ≤ M → P M → ¬ M.Connected →
      ∃ K : SimpleGraph V, M ≤ K ∧ P K ∧ M ≠ K) :
    ∃ M : SimpleGraph V, N ≤ M ∧ P M ∧ M.Connected := by sorry
