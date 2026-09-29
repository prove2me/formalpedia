-- Prove2me | Theorems.Thm_mme_stothers_lemma52_same_marginal
-- name    : mme_stothers_lemma52_same_marginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-29T00:20:26.232222+00:00
-- url     : https://prove2.me/theorems/21dbabd9-607e-4ea7-87c9-956b9b593a03
-- title:
--   Equation (5.2) and Lemma 5.2: same-marginal entropy correction
-- statement:
--   Let $Q:\mathbb R^{10}\to\mathbb R^9$ be the marginal map of Equation (5.2). First, its kernel is exactly the span of
--
--   $$
--   (0,0,1,0,-2,-2,0,2,0,-2),\qquad
--   (0,0,0,1,-2,0,-1,1,2,-2).
--   $$
--
--   Second, let $a,b\in\mathbb R^{10}$. Assume $a\in Z$, $b\in\mathcal N$, every coordinate of $b$ is strictly positive, and $a-b$ lies in that two-dimensional kernel. Then
--
--   $$
--   \prod_{i=1}^{10} b_i^{n_i b_i}
--   \le
--   \prod_{i=1}^{10} a_i^{n_i a_i}.
--   $$
--
--   The stationary set $\mathcal N$ is the subset of $Z$ satisfying
--   $b_3b_8^2=b_5b_6b_{10}$ and
--   $b_4b_8b_9=b_5b_7b_{10}$. These are the equations derived in Stothers's thesis and from the displayed kernel; they correct the inconsistent equations printed in the journal.
-- source:
--   Davie and Stothers (2013), Equation (5.2) and Lemma 5.2, printed pp. 367-368, https://www.maths.ed.ac.uk/~sandy/a11164.pdf; corrected stationary equations from Stothers thesis (2010), Chapter 4.2, printed pp. 78-79.

import Definitions.Def_mme_stothers_fourth_data

open MME BigOperators

set_option autoImplicit false

theorem mme_stothers_lemma52_same_marginal :
    (∀ x : Fin 10 → Real,
      (∀ j : Fin 9, MME.StothersFourth.Q x j = 0) ↔
        MME.StothersFourth.InY x) ∧
    (∀ a b : Fin 10 → Real,
      MME.StothersFourth.InZ a →
      MME.StothersFourth.InN b →
      (∀ i : Fin 10, 0 < b i) →
      MME.StothersFourth.InY (fun i => a i - b i) →
      MME.StothersFourth.entropyProduct b ≤
        MME.StothersFourth.entropyProduct a) := by
  sorry
