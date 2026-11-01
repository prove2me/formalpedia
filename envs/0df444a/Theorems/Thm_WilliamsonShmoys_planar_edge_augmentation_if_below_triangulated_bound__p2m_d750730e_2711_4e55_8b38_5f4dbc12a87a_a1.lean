-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_if_below_triangulated_bound__p2m_d750730e_2711_4e55_8b38_5f4dbc12a87a_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation_if_below_triangulated_bound__p2m_d750730e_2711_4e55_8b38_5f4dbc12a87a_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-31T21:59:39.004453+00:00
-- url     : https://prove2.me/theorems/609d0ef3-f673-413c-a21e-b454ce78643f
-- title:
--   Strict planar augmentation below the triangulated edge bound
-- statement:
--   If a drawable graph on at least three vertices has fewer than 3n−6 edges, it has a strictly larger drawable supergraph on the same vertex type.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_edge_augmentation_if_below_triangulated_bound__p2m_d750730e_2711_4e55_8b38_5f4dbc12a87a_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hW : HasPlanarDrawingOn W)
    (hcard : 3 ≤ Fintype.card V)
    (hbelow :
      letI : DecidableRel W.Adj := Classical.decRel W.Adj
      W.edgeFinset.card < 3 * Fintype.card V - 6) :
    ∃ X : SimpleGraph V, W ≤ X ∧ X ≠ W ∧ HasPlanarDrawingOn X := by sorry
