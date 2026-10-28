-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_edgeSet_superset
-- name    : WilliamsonShmoys.exists_maximal_edgeSet_superset
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T05:39:01.301993+00:00
-- url     : https://prove2.me/theorems/38d71976-5ed9-4646-935c-32d3097c60c6
-- title:
--   Finite maximal extension for an edge-deletion-closed property
-- statement:
--   On a finite vertex type, any property of graphs preserved by deleting edges has a maximal extension containing a given graph satisfying the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_edgeSet_superset
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ G H : SimpleGraph V,
      P H → G.edgeSet ⊆ H.edgeSet → P G)
    (K : SimpleGraph V)
    (hK : P K) :
    ∃ H : SimpleGraph V,
      P H ∧
      K.edgeSet ⊆ H.edgeSet ∧
      ∀ L : SimpleGraph V,
        P L → H.edgeSet ⊆ L.edgeSet → L.edgeSet ⊆ H.edgeSet := by sorry
