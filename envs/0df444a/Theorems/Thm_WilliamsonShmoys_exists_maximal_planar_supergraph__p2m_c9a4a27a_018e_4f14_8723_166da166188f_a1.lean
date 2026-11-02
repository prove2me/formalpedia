-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_c9a4a27a_018e_4f14_8723_166da166188f_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_c9a4a27a_018e_4f14_8723_166da166188f_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:57:38.418594+00:00
-- url     : https://prove2.me/theorems/ad4289f8-3c3e-4a88-885b-73372f5790e4
-- title:
--   Maximal drawable supergraph on the same vertices
-- statement:
--   Every drawable simple graph on a finite linearly ordered vertex type with at least three vertices has a drawable supergraph on the same vertices that is maximal among drawable supergraphs. Its edge count is at least the original graph’s edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_c9a4a27a_018e_4f14_8723_166da166188f_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    ∃ M : SimpleGraph V,
      H ≤ M ∧
      H.edgeFinset.card ≤ M.edgeFinset.card ∧
      HasPlanarDrawingOn M ∧
      ∀ N : SimpleGraph V, M ≤ N → HasPlanarDrawingOn N → N = M := by sorry
