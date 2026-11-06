-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_cut_separates_reachable_vertices__p2m_30445ffc_ee20_477d_a948_c780081d704c_a1
-- name    : WilliamsonShmoys.planar_drawing_cut_separates_reachable_vertices__p2m_30445ffc_ee20_477d_a948_c780081d704c_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:37:32.541338+00:00
-- url     : https://prove2.me/theorems/bc9d21a3-e9b7-4fa6-a15f-8ee7eb19a650
-- title:
--   An edge cut separates reachable vertices
-- statement:
--   For a partition of the vertices with no edge crossing its sides, a vertex on one side cannot be reachable from a vertex on the other.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_drawing_cut_separates_reachable_vertices__p2m_30445ffc_ee20_477d_a948_c780081d704c_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (A B : Set V)
    (hdisjoint : Disjoint A B) (hcover : A ∪ B = Set.univ)
    (hcut : ∀ u, u ∈ A → ∀ v, v ∈ B → ¬ K.Adj u v)
    (u v : V) (hu : u ∈ A) (hv : v ∈ B) :
    ¬ K.Reachable u v := by sorry
