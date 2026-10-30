-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_49a7b880_a3f8_443f_bfbf_c306626f3a20_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_49a7b880_a3f8_443f_bfbf_c306626f3a20_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T06:28:46.626161+00:00
-- url     : https://prove2.me/theorems/585fc207-795e-4bf8-b875-c8bd05631f21
-- title:
--   Maximal drawable graphs have the triangulated edge count
-- statement:
--   An inclusion-maximal drawable simple graph on at least three vertices has exactly 3|V|−6 edges. The proof route is to show maximality forces a connected triangulation, including for disconnected initial drawings, then apply Euler’s formula and count incidences between triangular faces and edges. At |V|=3 the conclusion is the triangle count 3; the formal proof must also handle this boundary case.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_49a7b880_a3f8_443f_bfbf_c306626f3a20_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      L ≤ M → WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L)
    (hCard : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard + 6 = 3 * Fintype.card V := by sorry
