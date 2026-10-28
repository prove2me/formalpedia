-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_cut_edge_extension
-- name    : WilliamsonShmoys.planar_cut_edge_extension
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T05:15:42.842692+00:00
-- url     : https://prove2.me/theorems/426f5976-5385-4824-8d9a-b659257f6fa1
-- title:
--   Add a planar bridge across an edge-free cut
-- statement:
--   If a planar graph has no edges crossing a vertex cut, then adding an edge between any selected vertices on opposite sides preserves planarity and strictly enlarges the edge set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem WilliamsonShmoys.planar_cut_edge_extension
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (A : Set V)
    (hCut : ∀ ⦃x y : V⦄, x ∈ A → y ∉ A → ¬ K.Adj x y)
    (u v : V)
    (hu : u ∈ A)
    (hv : v ∉ A) :
    ∃ L : SimpleGraph V,
      K.edgeSet ⊂ L.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
