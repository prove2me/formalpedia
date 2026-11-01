-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_across_separation__p2m_3eced331_e15d_452f_ac43_a684696313f5_a1
-- name    : WilliamsonShmoys.planar_drawing_add_edge_across_separation__p2m_3eced331_e15d_452f_ac43_a684696313f5_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:07:54.785571+00:00
-- url     : https://prove2.me/theorems/726a076b-6e45-45f6-9bfc-717031618dd6
-- title:
--   Add a bridge across a separated planar drawing
-- statement:
--   For a planar drawing whose vertices split into two nonempty sides with no original edge between the sides, adding exactly the edge between designated vertices on opposite sides preserves planarity. A proof route is to restrict to the two sides, redraw their connected components in separate regions with the designated vertices accessible to a joining arc, and then include that arc while keeping the other component drawings disjoint. This isolates the topological work from the parent’s reachability reasoning. The remaining core obligation is to justify this redrawing and arc construction for the exact continuous, injective, crossing-free arc conditions in `HasPlanarDrawingOn`.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_edge_across_separation__p2m_3eced331_e15d_452f_ac43_a684696313f5_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (u v : V) (A : Set V)
    (huA : u ∈ A) (hvA : v ∉ A)
    (hsep : ∀ a b, a ∈ A → b ∉ A → ¬ G.Adj a b) :
    ∃ H : SimpleGraph V,
      (∀ a b, H.Adj a b ↔
        G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
