-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_5ca561e0_6863_43fe_aa41_85fb9a3351ed_a1
-- name    : WilliamsonShmoys.maximal_planar_edge_count__p2m_5ca561e0_6863_43fe_aa41_85fb9a3351ed_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T07:26:38.985992+00:00
-- url     : https://prove2.me/theorems/f054e99a-40b4-4482-917a-34710df7f854
-- title:
--   Edge count of a maximal planar drawing
-- statement:
--   A drawable graph on at least three vertices that is inclusion-maximal among drawable graphs has exactly `3|V|−6` edges. The independent proof route is to show maximality forces every face in the planar embedding to be triangular, then combine Euler's formula with the face-edge incidence count. The hypothesis `3 ≤ |V|` is required for the maximal planar edge formula.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.maximal_planar_edge_count__p2m_5ca561e0_6863_43fe_aa41_85fb9a3351ed_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : forall L : SimpleGraph V,
      K <= L -> WilliamsonShmoys.HasPlanarDrawingOn L -> L = K)
    (hcard : 3 <= Fintype.card V) :
    letI : forall G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    K.edgeFinset.card = 3 * Fintype.card V - 6 := by sorry
