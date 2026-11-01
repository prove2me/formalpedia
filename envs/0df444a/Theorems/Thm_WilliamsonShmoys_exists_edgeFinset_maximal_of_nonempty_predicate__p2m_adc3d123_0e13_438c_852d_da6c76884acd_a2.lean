-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_edgeFinset_maximal_of_nonempty_predicate__p2m_adc3d123_0e13_438c_852d_da6c76884acd_a2
-- name    : WilliamsonShmoys.exists_edgeFinset_maximal_of_nonempty_predicate__p2m_adc3d123_0e13_438c_852d_da6c76884acd_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T02:56:47.019042+00:00
-- url     : https://prove2.me/theorems/3733edca-f120-4762-9766-2183cb052498
-- title:
--   Finite edge-maximal member of a graph family
-- statement:
--   Every nonempty family of simple graphs on a finite linearly ordered vertex type has a member with no proper edge-set extension inside the family.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem WilliamsonShmoys.exists_edgeFinset_maximal_of_nonempty_predicate__p2m_adc3d123_0e13_438c_852d_da6c76884acd_a2
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (hP : ∃ G, P G) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    ∃ G : SimpleGraph V,
      P G ∧
      ∀ H : SimpleGraph V,
        G.edgeFinset ⊆ H.edgeFinset →
        P H →
        H.edgeFinset ⊆ G.edgeFinset := by
  sorry
