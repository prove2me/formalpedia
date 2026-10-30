-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound_repair_20261026
-- name    : WilliamsonShmoys.maximal_planar_edge_lower_bound_repair_20261026
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:23:04.957594+00:00
-- url     : https://prove2.me/theorems/78f3a8dc-3bb1-4ff2-ae48-9ebfc46db80f
-- title:
--   Maximal planar drawing edge lower bound
-- statement:
--   A planar graph on at least three vertices whose edge set cannot be strictly extended while preserving planarity has at least 3|V|−6 edges. For three vertices, maximality forces all three edges. In larger cases, a proof can use maximality to establish connectedness and triangular faces, then count incidences using Euler’s formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_lower_bound_repair_20261026
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      K.edgeSet = L.edgeSet) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by sorry
