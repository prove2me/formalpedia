-- Prove2me | Theorems.Thm_exists_maximal_element_for_graph_predicate__p2m_a6c79c1c_4522_4952_80c8_2c98cd425351_a2
-- name    : exists_maximal_element_for_graph_predicate__p2m_a6c79c1c_4522_4952_80c8_2c98cd425351_a2
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-10-29T12:31:47.026694+00:00
-- url     : https://prove2.me/theorems/7f672717-7031-4c4a-b5fa-0f894e357dcc
-- title:
--   Maximal finite graph satisfying a predicate
-- statement:
--   For any predicate on simple graphs over a finite vertex type, every graph satisfying the predicate is contained in a predicate-satisfying graph whose edge set is maximal under inclusion.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

set_option autoImplicit false

theorem exists_maximal_element_for_graph_predicate__p2m_a6c79c1c_4522_4952_80c8_2c98cd425351_a2 {V : Type} [Fintype V] (P : SimpleGraph V → Prop) (M : SimpleGraph V) (hM : P M) : ∃ K : SimpleGraph V, P K ∧ M.edgeSet ⊆ K.edgeSet ∧ ∀ L : SimpleGraph V, P L → K.edgeSet ⊆ L.edgeSet → L.edgeSet ⊆ K.edgeSet := by sorry
