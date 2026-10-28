-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_for_finite_property
-- name    : WilliamsonShmoys.exists_maximal_supergraph_for_finite_property
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-27T17:25:09.207011+00:00
-- url     : https://prove2.me/theorems/6f88a87d-9201-4500-a611-97fb282f833b
-- title:
--   Finite maximal supergraph for a graph property
-- statement:
--   For any property of simple graphs on a finite linearly ordered vertex type, every graph satisfying the property has a supergraph satisfying it that is maximal under edge inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_supergraph_for_finite_property
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop) (H : SimpleGraph V) (hH : P H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      P K ∧
      ∀ L : SimpleGraph V,
        K.edgeSet ⊆ L.edgeSet → K.edgeSet ≠ L.edgeSet → ¬ P L := by sorry
