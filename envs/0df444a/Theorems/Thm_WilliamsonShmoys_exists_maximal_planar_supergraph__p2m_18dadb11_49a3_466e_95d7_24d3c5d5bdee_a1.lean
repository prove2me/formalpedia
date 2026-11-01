-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_18dadb11_49a3_466e_95d7_24d3c5d5bdee_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_18dadb11_49a3_466e_95d7_24d3c5d5bdee_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T01:49:49.750274+00:00
-- url     : https://prove2.me/theorems/ba215390-0e6f-4354-a4af-e10f8512e984
-- title:
--   Existence of a maximal drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type is contained in a drawable supergraph that has no strict drawable supergraph on the same vertices. The claim also covers types with fewer than three vertices.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_18dadb11_49a3_466e_95d7_24d3c5d5bdee_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L = K := by sorry
