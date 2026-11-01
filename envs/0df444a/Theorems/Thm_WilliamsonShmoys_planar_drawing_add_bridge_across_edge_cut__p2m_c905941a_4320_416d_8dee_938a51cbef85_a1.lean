-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_add_bridge_across_edge_cut__p2m_c905941a_4320_416d_8dee_938a51cbef85_a1
-- name    : WilliamsonShmoys.planar_drawing_add_bridge_across_edge_cut__p2m_c905941a_4320_416d_8dee_938a51cbef85_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T02:24:25.682025+00:00
-- url     : https://prove2.me/theorems/30445ffc-ee20-477d-a948-c780081d704c
-- title:
--   Add a planar bridge across an edge cut
-- statement:
--   Given a planar drawing and a partition into two nonempty sides with no edge crossing the partition, add an edge between the sides while preserving planarity. This isolates the geometric work of the target: redraw the two planar pieces separately and route an arc between chosen vertices through the exterior. The cut also ensures that the chosen cross-side vertices were not already reachable.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_add_bridge_across_edge_cut__p2m_c905941a_4320_416d_8dee_938a51cbef85_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn K)
    (A B : Set V)
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hdisjoint : Disjoint A B) (hcover : A ∪ B = Set.univ)
    (hcut : ∀ u, u ∈ A → ∀ v, v ∈ B → ¬ K.Adj u v) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet ∧
      (∃ u v, ¬ K.Reachable u v ∧ L.Adj u v) ∧
      HasPlanarDrawingOn L := by sorry
