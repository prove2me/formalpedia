-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_maximal_supergraph_of_finite_predicate__p2m_a06f5bd4_9714_4d93_b157_09922cf717e8_a1
-- name    : WilliamsonShmoys.exists_maximal_supergraph_of_finite_predicate__p2m_a06f5bd4_9714_4d93_b157_09922cf717e8_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T17:39:14.001334+00:00
-- url     : https://prove2.me/theorems/b2e11005-0f41-4e7a-b869-81b271552bcf
-- title:
--   Finite maximality for graph predicates
-- statement:
--   For a finite linearly ordered vertex type, any graph satisfying a property P has a P-satisfying supergraph that is maximal among P-satisfying supergraphs under edge inclusion. The proof selects an admissible supergraph with the largest finite edge count.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem WilliamsonShmoys.exists_maximal_supergraph_of_finite_predicate__p2m_a06f5bd4_9714_4d93_b157_09922cf717e8_a1
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (P : SimpleGraph V → Prop) (hP : P H) :
    Exists fun K : SimpleGraph V =>
      And (LE.le H K) (And (P K)
        (forall L : SimpleGraph V, LE.le K L -> P L -> Eq L K)) := by sorry
