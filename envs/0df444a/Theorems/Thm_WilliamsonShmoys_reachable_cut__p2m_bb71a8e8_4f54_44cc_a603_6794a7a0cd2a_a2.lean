-- Prove2me | Theorems.Thm_WilliamsonShmoys_reachable_cut__p2m_bb71a8e8_4f54_44cc_a603_6794a7a0cd2a_a2
-- name    : WilliamsonShmoys.reachable_cut__p2m_bb71a8e8_4f54_44cc_a603_6794a7a0cd2a_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:47:13.629116+00:00
-- url     : https://prove2.me/theorems/0d507daa-6a22-4a15-847b-ad2211f08977
-- title:
--   Reachability defines an edge-free cut
-- statement:
--   The vertices reachable from `u` form a set containing `u` and excluding `v`; no edge crosses from that set to its complement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

theorem WilliamsonShmoys.reachable_cut__p2m_bb71a8e8_4f54_44cc_a603_6794a7a0cd2a_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {u v : V} (hdis : ¬ G.Reachable u v) :
    ∃ A : Set V, u ∈ A ∧ v ∉ A ∧
      ∀ ⦃x y : V⦄, x ∈ A → y ∉ A → ¬ G.Adj x y := by sorry
