-- Prove2me | Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_b24ee22a_ee0a_4874_a748_da2528ed7758
-- name    : WilliamsonShmoys.maximal_planar_edge_count_b24ee22a_ee0a_4874_a748_da2528ed7758
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-27T06:11:02.225254+00:00
-- url     : https://prove2.me/theorems/0f8e2e00-938f-48dd-b9df-c9c436c8a851
-- title:
--   Edge count of an inclusion-maximal drawable graph
-- statement:
--   If a drawable graph on at least three vertices is inclusion-maximal among drawable graphs on that same vertex type, its edge count is three times the number of vertices minus six.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.maximal_planar_edge_count_b24ee22a_ee0a_4874_a748_da2528ed7758
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V, K ≤ L →
      WilliamsonShmoys.HasPlanarDrawingOn L → L ≤ K)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = K.edgeSet.ncard + 6 := by sorry
