-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count__p2m_878ddd3e_03fb_448c_a8d8_103ff049e818_a1
-- name    : WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_878ddd3e_03fb_448c_a8d8_103ff049e818_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T22:31:11.524715+00:00
-- url     : https://prove2.me/theorems/1258d26f-3604-445e-9011-471047f5700d
-- title:
--   Edge count of a maximal drawable graph
-- statement:
--   If a drawable finite simple graph with at least three vertices has no strictly larger drawable supergraph on the same vertex set, then it has exactly 3|V|−6 edges. This is the Euler triangulation count: maximality forces triangular faces, after which Euler’s formula gives the count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_878ddd3e_03fb_448c_a8d8_103ff049e818_a1 {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V) (hK : HasPlanarDrawingOn K) (hmax : ∀ L : SimpleGraph V, K ≤ L → HasPlanarDrawingOn L → L ≤ K) (hV : 3 ≤ Fintype.card V) : K.edgeSet.ncard = 3 * Fintype.card V - 6 := by sorry
