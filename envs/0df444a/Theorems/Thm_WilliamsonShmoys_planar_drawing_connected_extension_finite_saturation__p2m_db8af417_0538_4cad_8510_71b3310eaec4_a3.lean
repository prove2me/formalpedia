-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_finite_saturation__p2m_db8af417_0538_4cad_8510_71b3310eaec4_a3
-- name    : WilliamsonShmoys.planar_drawing_connected_extension_finite_saturation__p2m_db8af417_0538_4cad_8510_71b3310eaec4_a3
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:23:30.847505+00:00
-- url     : https://prove2.me/theorems/fc3eb67c-27b1-410c-a6c3-58b4eed00365
-- title:
--   Finite saturation under strict extension
-- statement:
--   For a property of graphs on a finite vertex type, if every disconnected graph with the property has a strictly larger supergraph with the property, then every such input has a connected supergraph with at least as many edges. This removes the finite maximization and edge-count argument from the parent; it can be proved by maximizing over the finite family of qualifying supergraphs and applying the strict-extension hypothesis to a disconnected maximizer.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_connected_extension_finite_saturation__p2m_db8af417_0538_4cad_8510_71b3310eaec4_a3
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hStep : ∀ G : SimpleGraph V, P G → ¬ G.Connected →
      ∃ H : SimpleGraph V, G ≤ H ∧ P H ∧ H ≠ G)
    (G : SimpleGraph V)
    (hG : P G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ P H ∧ H.Connected ∧
      (G.edgeSet.ncard : Int) ≤ (H.edgeSet.ncard : Int) := by sorry
