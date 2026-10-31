-- Prove2me | Theorems.Thm_finite_maximal_supergraph_of_property__p2m_aab4ced3_2cb3_4a94_814b_7026a53a954f_a2
-- name    : finite_maximal_supergraph_of_property__p2m_aab4ced3_2cb3_4a94_814b_7026a53a954f_a2
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-30T09:41:44.273542+00:00
-- url     : https://prove2.me/theorems/fc9c7b34-2592-45bb-b8b0-1c28dec1ee49
-- title:
--   Finite maximal supergraph for a property
-- statement:
--   For a finite vertex type, any graph satisfying a property has an inclusion-maximal extension that also satisfies the property.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem finite_maximal_supergraph_of_property__p2m_aab4ced3_2cb3_4a94_814b_7026a53a954f_a2
    {V : Type} [Fintype V] (M : SimpleGraph V)
    (P : SimpleGraph V -> Prop) (hM : P M) :
    Exists fun N : SimpleGraph V =>
      M <= N /\ P N /\
        (forall Q : SimpleGraph V, N <= Q -> P Q -> Q = N) := by sorry
