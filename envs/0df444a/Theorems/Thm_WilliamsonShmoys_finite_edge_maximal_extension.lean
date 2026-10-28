-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_edge_maximal_extension
-- name    : WilliamsonShmoys.finite_edge_maximal_extension
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T20:40:48.100869+00:00
-- url     : https://prove2.me/theorems/26b41c1d-882f-4682-839d-a5f130957f4d
-- title:
--   Finite maximal extension for a hereditary graph property
-- statement:
--   For any predicate on simple graphs over a finite vertex type that is preserved when edges are removed, every graph satisfying the predicate has a supergraph satisfying it that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.finite_edge_maximal_extension
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {G H : SimpleGraph V}, G.edgeSet ⊆ H.edgeSet → P H → P G)
    (J : SimpleGraph V) (hJ : P J) :
    ∃ K : SimpleGraph V, J.edgeSet ⊆ K.edgeSet ∧ P K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → P L → L = K := by sorry
