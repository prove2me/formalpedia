-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_bridge_reachable_cut__p2m_016bc9c9_be0e_41b2_afe4_acfa54df6433_a1
-- name    : WilliamsonShmoys.planar_bridge_reachable_cut__p2m_016bc9c9_be0e_41b2_afe4_acfa54df6433_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:20:46.107073+00:00
-- url     : https://prove2.me/theorems/3a4466d4-b823-4bbf-955d-e3ebcc5a37f3
-- title:
--   Reachability defines an edge-free cut
-- statement:
--   For unreachable vertices, the connected component of the first vertex contains it, excludes the second, and has no graph edge crossing between it and its complement.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_bridge_reachable_cut__p2m_016bc9c9_be0e_41b2_afe4_acfa54df6433_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) {u v : V}
    (hUnreachable : ¬ G.Reachable u v) :
    ∃ s : Set V, u ∈ s ∧ v ∉ s ∧
      ∀ x y, G.Adj x y → (x ∈ s ↔ y ∈ s) := by sorry
