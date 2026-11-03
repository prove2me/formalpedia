-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_euler_edge_bound__p2m_06e45311_b4a8_47cf_99af_36dad6983f39_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_euler_edge_bound__p2m_06e45311_b4a8_47cf_99af_36dad6983f39_a1
-- status  : Disproved
-- author  : @Eyal1990
-- created : 2026-11-01T02:21:50.696074+00:00
-- url     : https://prove2.me/theorems/d0cbf8fc-b126-4e9b-9c59-f16faa272cb9
-- title:
--   Euler edge count for a maximal planar drawing
-- statement:
--   A finite simple graph on at least three vertices that is edge-maximal among graphs with a drawing of the specified kind has exactly 3|V|−6 edges.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_drawing_euler_edge_bound__p2m_06e45311_b4a8_47cf_99af_36dad6983f39_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ H' : SimpleGraph V,
      (∀ {u v : V}, H'.Adj u v → H.Adj u v) →
      HasPlanarDrawingOn H' → H' = H) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    H.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
