-- Prove2me | Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_07b4009a_04ca_4342_a9d5_b274d08c0821_a1
-- name    : WilliamsonShmoys.planar_maximal_supergraph__p2m_07b4009a_04ca_4342_a9d5_b274d08c0821_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T06:39:18.981935+00:00
-- url     : https://prove2.me/theorems/9e5fb9d2-aa0e-41c4-9a80-cb078400c4e8
-- title:
--   Existence of an edge-maximal drawable supergraph
-- statement:
--   Every drawable finite simple graph has a drawable edge-maximal supergraph on the same vertex type. This is the finite maximality step: among the finitely many edge sets of drawable supergraphs, select one with maximum cardinality.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.planar_maximal_supergraph__p2m_07b4009a_04ca_4342_a9d5_b274d08c0821_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G) :
    letI : ∀ H : SimpleGraph V, DecidableRel H.Adj :=
      fun H => Classical.decRel H.Adj
    ∃ H : SimpleGraph V,
      G.edgeFinset ⊆ H.edgeFinset ∧
      HasPlanarDrawingOn H ∧
      ∀ K : SimpleGraph V,
        H.edgeFinset ⊆ K.edgeFinset →
        HasPlanarDrawingOn K →
        K.edgeFinset ⊆ H.edgeFinset := by
  sorry
