-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_cut_bridge__p2m_0b5c6abe_9063_498b_b66b_6e8d4f2b2880_a2
-- name    : WilliamsonShmoys.planar_drawing_cut_bridge__p2m_0b5c6abe_9063_498b_b66b_6e8d4f2b2880_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T20:57:56.758093+00:00
-- url     : https://prove2.me/theorems/9a2bae5c-cda3-4fda-a7e2-a764b5d323bb
-- title:
--   Add a bridge across an edge-free cut in a planar drawing
-- statement:
--   For any planar drawing and any cut with no original edge crossing it, adding the single edge between vertices on opposite sides preserves the existence of a planar drawing. This is the reusable geometric step: re-embed the connected components with the designated endpoints on outer faces, separate the component drawings, and route a simple arc between those endpoints through the exterior. It retains the parent’s exact edge relation and drawing predicate; establishing this topological construction is the remaining core obligation.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_cut_bridge__p2m_0b5c6abe_9063_498b_b66b_6e8d4f2b2880_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (S : Set V) (u v : V)
    (hu : u ∈ S) (hv : v ∉ S)
    (hcut : ∀ ⦃a b : V⦄, a ∈ S → b ∉ S → ¬ G.Adj a b) :
    ∃ H : SimpleGraph V,
      (∀ a b, H.Adj a b ↔
        G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  sorry
