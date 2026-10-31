-- Prove2me | Theorems.Thm_exists_maximal_mem_of_finite__p2m_4f4a8988_3a83_4c97_870a_3e268ffa4b52_a1
-- name    : exists_maximal_mem_of_finite__p2m_4f4a8988_3a83_4c97_870a_3e268ffa4b52_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-30T05:45:46.761108+00:00
-- url     : https://prove2.me/theorems/7c4bf9f3-59e8-4e7c-b88c-9e17cdfb6b94
-- title:
--   A nonempty subset of a finite partial order has a maximal member
-- statement:
--   Every nonempty subset of a finite partial order contains an element with no distinct larger member in that subset. This supplies the maximal planar supergraph after taking the order to be graph inclusion and the subset predicate to mean “extends K and has a planar drawing.”
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_mem_of_finite__p2m_4f4a8988_3a83_4c97_870a_3e268ffa4b52_a1
    {alpha : Type} [Fintype alpha] [PartialOrder alpha]
    (P : alpha -> Prop)
    (hne : exists a, P a) :
    exists a, P a /\ forall b, a <= b -> P b -> b = a := by sorry
