-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_maximal_drawable_supergraph__p2m_cb71297e_2af2_47af_8fd1_d009bcc4ef4e_a2
-- name    : WilliamsonShmoys.finite_maximal_drawable_supergraph__p2m_cb71297e_2af2_47af_8fd1_d009bcc4ef4e_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T10:40:52.729384+00:00
-- url     : https://prove2.me/theorems/5c5ff357-b4a7-43ef-ab24-576229740c5b
-- title:
--   Existence of a finite maximal drawable supergraph
-- statement:
--   On a finite ordered vertex type, every graph with a planar drawing has a drawable supergraph that is maximal under inclusion among drawable supergraphs. The chosen supergraph also has at least as many edges as the original graph.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.finite_maximal_drawable_supergraph__p2m_cb71297e_2af2_47af_8fd1_d009bcc4ef4e_a2
    {V : Type} [Fintype V] [LinearOrder V] (K : SimpleGraph V)
    (hK : HasPlanarDrawingOn K) :
    ∃ H : SimpleGraph V, K ≤ H ∧ HasPlanarDrawingOn H ∧
      K.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J ≤ H := by sorry
