-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_triangulated_planar_extension__p2m_7b40ef00_72b0_4fde_a3cb_cf2325177ae8_a1
-- name    : WilliamsonShmoys.exists_triangulated_planar_extension__p2m_7b40ef00_72b0_4fde_a3cb_cf2325177ae8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-28T20:47:45.354215+00:00
-- url     : https://prove2.me/theorems/68514819-a212-4a71-843f-93b3ee5d7783
-- title:
--   Triangulated extension of a finite planar drawing
-- statement:
--   Every finite drawable simple graph on at least three vertices has a drawable supergraph on the same vertices with exactly 3|V| − 6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys
set_option autoImplicit false

/-- Mathematical route: add noncrossing edges until the planar regions are triangular, then use Euler's formula and face-edge incidence counting. The formal work is to establish this route for the given `HasPlanarDrawingOn` definition. -/

theorem WilliamsonShmoys.exists_triangulated_planar_extension__p2m_7b40ef00_72b0_4fde_a3cb_cf2325177ae8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
        3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
