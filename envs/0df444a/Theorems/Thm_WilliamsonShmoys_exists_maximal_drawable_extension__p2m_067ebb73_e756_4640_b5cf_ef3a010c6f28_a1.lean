-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_extension__p2m_067ebb73_e756_4640_b5cf_ef3a010c6f28_a1
-- name    : WilliamsonShmoys.exists_maximal_drawable_extension__p2m_067ebb73_e756_4640_b5cf_ef3a010c6f28_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:36:31.457001+00:00
-- url     : https://prove2.me/theorems/48dfa0b2-3288-4dee-b204-30af943e5fa4
-- title:
--   A drawable graph has a maximum drawable supergraph
-- statement:
--   Every drawable graph on a finite vertex type has a drawable supergraph on that same type whose edge count is at least as large and is maximum among drawable supergraphs. This removes the finite choice and maximality setup from the parent. Independently, enumerate the finitely many simple graphs on V, restrict to drawable supergraphs of Q, and choose one with maximum edge count; Q ensures the candidate set is nonempty.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem WilliamsonShmoys.exists_maximal_drawable_extension__p2m_067ebb73_e756_4640_b5cf_ef3a010c6f28_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V) (hQ : HasPlanarDrawingOn Q) :
    ∃ R : SimpleGraph V,
      (∀ u v, Q.Adj u v → R.Adj u v) ∧
      HasPlanarDrawingOn R ∧
      (letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
       letI : DecidableRel R.Adj := Classical.decRel R.Adj
       Q.edgeFinset.card ≤ R.edgeFinset.card) ∧
      (∀ S : SimpleGraph V, (∀ u v, R.Adj u v → S.Adj u v) →
        HasPlanarDrawingOn S →
        (letI : DecidableRel S.Adj := Classical.decRel S.Adj
         letI : DecidableRel R.Adj := Classical.decRel R.Adj
         S.edgeFinset.card ≤ R.edgeFinset.card)) := by sorry
