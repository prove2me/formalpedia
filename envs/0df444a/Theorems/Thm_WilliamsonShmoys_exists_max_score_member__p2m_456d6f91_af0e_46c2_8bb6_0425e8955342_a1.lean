-- Prove2me | Theorems.Thm_WilliamsonShmoys_exists_max_score_member__p2m_456d6f91_af0e_46c2_8bb6_0425e8955342_a1
-- name    : WilliamsonShmoys.exists_max_score_member__p2m_456d6f91_af0e_46c2_8bb6_0425e8955342_a1
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-11-01T06:38:44.407562+00:00
-- url     : https://prove2.me/theorems/ff75b116-93bf-40af-b9b4-4091fd456659
-- title:
--   A nonempty finite predicate has a maximum-score member
-- statement:
--   For a finite type, any predicate with at least one satisfying element has a satisfying element whose natural-number score is at least that of every other satisfying element.
-- source:
--   David P. Williamson and David B. Shmoys, The Design of Approximation Algorithms, Cambridge University Press, 2011, author electronic manuscript, Section 10.2, proof of Theorem 10.11, pp. 270-272. https://doi.org/10.1017/CBO9780511921735. Bounded tree-width of the pieces: Robertson–Seymour (planar graphs of radius r have tree-width at most 3r+1) / Bodlaender (k-outerplanar graphs have tree-width at most 3k-1).

import Mathlib

theorem WilliamsonShmoys.exists_max_score_member__p2m_456d6f91_af0e_46c2_8bb6_0425e8955342_a1
    {α : Type} [Fintype α]
    (P : α → Prop) (score : α → Nat) (a : α) (ha : P a) :
    ∃ b, P b ∧ ∀ c, P c → score c ≤ score b := by
  sorry
