-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_graph_extension_connected__p2m_a6ee2644_08f0_4c4d_a139_48d0925fab45_a1
-- name    : WilliamsonShmoys.finite_graph_extension_connected__p2m_a6ee2644_08f0_4c4d_a139_48d0925fab45_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:08:18.773308+00:00
-- url     : https://prove2.me/theorems/14d35ba9-f71b-48d0-891e-b30c00ebf4b2
-- title:
--   Finite strict extensions yield a connected supergraph
-- statement:
--   For a finite vertex type, if every disconnected Good graph has a strictly larger Good supergraph, then every Good starting graph has a connected Good supergraph containing it. Prove this by choosing a maximal Good supergraph from the finite set of simple graphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_graph_extension_connected__p2m_a6ee2644_08f0_4c4d_a139_48d0925fab45_a1
    {V : Type} [Fintype V]
    (Good : SimpleGraph V → Prop)
    (N : SimpleGraph V)
    (hN : Good N)
    (extend : ∀ (G : SimpleGraph V), Good G → ¬ G.Connected →
      ∃ P : SimpleGraph V, G ≤ P ∧ G ≠ P ∧ Good P) :
    ∃ P : SimpleGraph V, N ≤ P ∧ P.Connected ∧ Good P := by sorry
