-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
-- name    : WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T12:19:41.612448+00:00
-- url     : https://prove2.me/theorems/d833d204-1cac-48ce-b1ff-fc91bbaabed8
-- title:
--   Extend a planar drawing to a maximal planar supergraph
-- statement:
--   On the same finite vertex type, every drawable graph with at least three vertices is contained in a drawable graph maximal among drawable simple supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_56609264_6a9a_4229_a716_b7a8ddd670b3_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ H : SimpleGraph V, L ≤ H ∧ HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H := by sorry
