-- Prove2me | Theorems.Thm_finite_strict_relation_has_maximal__p2m_d8caa262_4f2a_4c35_a872_b5a837a56723_a2
-- name    : finite_strict_relation_has_maximal__p2m_d8caa262_4f2a_4c35_a872_b5a837a56723_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T07:02:58.89643+00:00
-- url     : https://prove2.me/theorems/aa2ed7b2-e5b5-47c6-b60a-ae10e8c8df10
-- title:
--   A finite strict transitive relation has a maximal element
-- statement:
--   Every nonempty finite set equipped with an irreflexive transitive relation contains an element with no related successor in the set. This removes the finite maximality argument from the parent; prove it by induction on the size of the set, using transitivity and irreflexivity to rule out an endless chain of strict successors. In the parent, instantiate the relation with strict extension of planar supergraphs. The remaining obligations are candidate membership, monotonicity of connectedness under graph inclusion, and applying maximality to each planar extension.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib
set_option autoImplicit false

theorem finite_strict_relation_has_maximal__p2m_d8caa262_4f2a_4c35_a872_b5a837a56723_a2 {α : Type} [Fintype α] [DecidableEq α] (s : Finset α) (r : α → α → Prop) (hne : s.Nonempty) (hirr : ∀ a, ¬ r a a) (htrans : ∀ a b c, r a b → r b c → r a c) : ∃ a, a ∈ s ∧ ∀ b, b ∈ s → ¬ r a b := by sorry
