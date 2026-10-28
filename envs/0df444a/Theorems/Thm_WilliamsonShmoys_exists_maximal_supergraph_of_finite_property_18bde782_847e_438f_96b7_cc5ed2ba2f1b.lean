-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_property_18bde782_847e_438f_96b7_cc5ed2ba2f1b
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_finite_property_18bde782_847e_438f_96b7_cc5ed2ba2f1b
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-26T04:29:50.2151+00:00
-- url     : https://prove2.me/theorems/32d658f4-7011-4415-bcdd-54416853c48b
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   On a finite vertex type, every graph satisfying a property has a supergraph satisfying that property which is maximal among such supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_maximal_supergraph_of_finite_property_18bde782_847e_438f_96b7_cc5ed2ba2f1b
    {V : Type} [Fintype V]
    (L : SimpleGraph V)
    (P : SimpleGraph V → Prop)
    (hL : P L) :
    ∃ T : SimpleGraph V,
      L ≤ T ∧ P T ∧
        ∀ U : SimpleGraph V, T ≤ U → P U → U ≤ T := by sorry
