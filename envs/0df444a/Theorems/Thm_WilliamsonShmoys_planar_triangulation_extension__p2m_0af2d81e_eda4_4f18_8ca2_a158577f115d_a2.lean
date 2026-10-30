-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_triangulation_extension__p2m_0af2d81e_eda4_4f18_8ca2_a158577f115d_a2
-- name    : WilliamsonShmoys.planar_triangulation_extension__p2m_0af2d81e_eda4_4f18_8ca2_a158577f115d_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T00:59:31.700033+00:00
-- url     : https://prove2.me/theorems/33fe1755-151f-4b39-a9dc-13183099c0e1
-- title:
--   Extend a planar drawing to a triangulation
-- statement:
--   For a crossing-free drawing of a finite simple graph on at least three vertices, there is a planar supergraph on the same vertex set whose edge count is exactly 3|V|−6, with adjacency decidability supplied for that count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.planar_triangulation_extension__p2m_0af2d81e_eda4_4f18_8ca2_a158577f115d_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hL : HasPlanarDrawingOn L)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ M : SimpleGraph V,
      L ≤ M ∧ HasPlanarDrawingOn M ∧
        ∃ (dM : DecidableRel M.Adj),
          (letI : DecidableRel M.Adj := dM;
            M.edgeFinset.card = 3 * Fintype.card V - 6) := by sorry
