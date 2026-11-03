-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation_below_triangulation_bound__p2m_a09da42e_0803_4d50_ab6c_6ed525cd351e_a1
-- name    : WilliamsonShmoys.planar_drawing_edge_augmentation_below_triangulation_bound__p2m_a09da42e_0803_4d50_ab6c_6ed525cd351e_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:38:45.160232+00:00
-- url     : https://prove2.me/theorems/7802999e-536b-4f03-9f51-584d07594d0b
-- title:
--   Planar edge augmentation below the triangulation bound
-- statement:
--   If a finite graph on at least three vertices has a crossing-free drawing and fewer than 3|V|−6 edges, some missing edge can be added while preserving a crossing-free drawing.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.planar_drawing_edge_augmentation_below_triangulation_bound__p2m_a09da42e_0803_4d50_ab6c_6ed525cd351e_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L)
    (hSparse : (letI : DecidableRel L.Adj := Classical.decRel L.Adj;
      L.edgeFinset.card + 6 < 3 * Fintype.card V)) :
    ∃ M : SimpleGraph V, L ≤ M ∧ M ≠ L ∧ HasPlanarDrawingOn M := by sorry
