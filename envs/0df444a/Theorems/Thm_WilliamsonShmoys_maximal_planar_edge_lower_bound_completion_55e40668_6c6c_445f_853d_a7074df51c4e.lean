-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_completion_55e40668_6c6c_445f_853d_a7074df51c4e
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_completion_55e40668_6c6c_445f_853d_a7074df51c4e
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T00:32:36.566711+00:00
-- url     : https://prove2.me/theorems/ea86fb8c-626b-4602-b4df-ce0f5d3fdec6
-- title:
--   Inclusion-maximal planar graph edge lower bound
-- statement:
--   An inclusion-maximal simply drawn planar graph on at least three vertices has at least 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_completion_55e40668_6c6c_445f_853d_a7074df51c4e
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M = L)
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V - 6 ≤ L.edgeSet.ncard := by sorry
