-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_bridge_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a1
-- name    : WilliamsonShmoys.planar_bridge_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:05:50.600041+00:00
-- url     : https://prove2.me/theorems/0c3f32ed-165d-4d2a-9c18-4c03449c5c6d
-- title:
--   Non-reachability gives an edge-separated partition
-- statement:
--   If `u` and `v` are not reachable, the reachable set of `u` and its complement partition the vertices, separate `u` from `v`, and have no graph edge crossing between them.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.planar_bridge_partition__p2m_c25e31c2_3944_4e71_be02_9fbfc136a4b1_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (u v : V) (hnot : ¬ G.Reachable u v) :
    ∃ A B : Set V,
      (∀ x, x ∈ A ∨ x ∈ B) ∧
      Disjoint A B ∧
      u ∈ A ∧
      v ∈ B ∧
      (∀ x y, G.Adj x y → (x ∈ A ↔ y ∈ A)) := by sorry
