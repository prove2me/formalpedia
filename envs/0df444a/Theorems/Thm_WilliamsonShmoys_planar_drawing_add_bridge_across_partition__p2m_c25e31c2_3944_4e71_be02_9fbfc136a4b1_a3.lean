-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_across_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3
-- name    : WilliamsonShmoys.planar_drawing_add_bridge_across_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:31:08.814971+00:00
-- url     : https://prove2.me/theorems/d5d24b34-bbce-435b-8e9b-b760a80388a7
-- title:
--   Add a bridge across edge-separated planar parts
-- statement:
--   Given planar drawings of two disjoint, edge-separated parts, construct a planar drawing after adding an edge between a selected vertex in each part.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_add_bridge_across_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a3
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (A B : Set V) (u v : V)
    [Fintype A] [LinearOrder A] [Fintype B] [LinearOrder B]
    (hA : WilliamsonShmoys.HasPlanarDrawingOn (G.induce A))
    (hB : WilliamsonShmoys.HasPlanarDrawingOn (G.induce B))
    (hcover : ∀ x, x ∈ A ∨ x ∈ B)
    (hdisjoint : Disjoint A B)
    (hcross : ∀ x y, G.Adj x y → (x ∈ A ↔ y ∈ A))
    (hu : u ∈ A) (hv : v ∈ B) :
    ∃ H : SimpleGraph V,
      (∀ a b, H.Adj a b ↔
        G.Adj a b ∨ ((a = u ∧ b = v) ∨ (a = v ∧ b = u))) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by sorry
