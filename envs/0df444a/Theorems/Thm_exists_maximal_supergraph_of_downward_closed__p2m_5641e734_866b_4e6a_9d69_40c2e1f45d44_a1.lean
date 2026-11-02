-- Prove2me | Theorems.Thm_exists_maximal_supergraph_of_downward_closed__p2m_5641e734_866b_4e6a_9d69_40c2e1f45d44_a1
-- name    : exists_maximal_supergraph_of_downward_closed__p2m_5641e734_866b_4e6a_9d69_40c2e1f45d44_a1
-- status  : Proved
-- author  : @Eyal1990
-- created : 2026-11-01T16:44:23.508748+00:00
-- url     : https://prove2.me/theorems/58eb863c-546e-468e-a5b9-34ab4d2e586b
-- title:
--   Finite maximal extension for a downward-closed graph property
-- statement:
--   For a finite vertex type, every graph satisfying a downward-closed property is contained in a satisfying supergraph that is maximal among satisfying supergraphs.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem exists_maximal_supergraph_of_downward_closed__p2m_5641e734_866b_4e6a_9d69_40c2e1f45d44_a1
    {V : Type} [Fintype V] [DecidableEq V]
    (P : SimpleGraph V → Prop)
    (hdown : ∀ {A B : SimpleGraph V}, A ≤ B → P B → P A)
    (G : SimpleGraph V) (hG : P G) :
    ∃ K : SimpleGraph V, G ≤ K ∧ P K ∧
      ∀ H : SimpleGraph V, K ≤ H → P H → H ≤ K := by sorry
