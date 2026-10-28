-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_edge_augmentation_below_bound__p2m_03ed2ab0_efc9_4bea_b7ff_50f9e41807dc_a1
-- name    : WilliamsonShmoys.planar_edge_augmentation_below_bound__p2m_03ed2ab0_efc9_4bea_b7ff_50f9e41807dc_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-28T18:33:45.641194+00:00
-- url     : https://prove2.me/theorems/96b612ce-7021-404c-8189-06955c76f0dc
-- title:
--   Augmenting a drawable graph below the planar edge bound
-- statement:
--   If a drawable simple graph on at least three vertices has fewer than 3|V|−6 edges, it has a strict drawable supergraph on the same vertex set.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_edge_augmentation_below_bound__p2m_03ed2ab0_efc9_4bea_b7ff_50f9e41807dc_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hCard : 3 ≤ Fintype.card V)
    (hBelow : K.edgeSet.ncard + 6 < 3 * Fintype.card V) :
    ∃ L : SimpleGraph V, K < L ∧ WilliamsonShmoys.HasPlanarDrawingOn L := by sorry
