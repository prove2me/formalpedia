-- Prove2me | Theorems.Thm_WilliamsonShmoys_finite_property_maximal_extension__p2m_d19fe924_8be5_4905_9de7_834ee0c8d168_a1
-- name    : WilliamsonShmoys.finite_property_maximal_extension__p2m_d19fe924_8be5_4905_9de7_834ee0c8d168_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:05:51.73272+00:00
-- url     : https://prove2.me/theorems/1179c870-19f7-45a9-afef-7015b20cd6a7
-- title:
--   Finite maximal extension for a graph property
-- statement:
--   For any property of simple graphs on a finite vertex type, every graph satisfying the property is contained in an edge-maximal graph satisfying it.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.finite_property_maximal_extension__p2m_d19fe924_8be5_4905_9de7_834ee0c8d168_a1
    {V : Type} [Fintype V]
    (P : SimpleGraph V → Prop)
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : P H) :
    ∃ (K : SimpleGraph V) (dK : DecidableRel K.Adj),
      (letI : DecidableRel K.Adj := dK
       P K ∧
       (∀ (L : SimpleGraph V) [DecidableRel L.Adj],
         P L →
         K.edgeFinset ⊆ L.edgeFinset →
         K.edgeFinset = L.edgeFinset) ∧
       H.edgeFinset ⊆ K.edgeFinset) := by sorry
