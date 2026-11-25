-- Prove2me | Theorems.Thm_collatz_smaller_merger_from_variable_dyadic_relay
-- name    : collatz_smaller_merger_from_variable_dyadic_relay
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:04:09.593509+00:00
-- url     : https://prove2.me/theorems/72a5ff0e-f986-56f0-ba7d-4a57371ebf47
-- title:
--   A smaller Collatz merger through a variable dyadic relay
-- statement:
--   Let $C$ be the ordinary Collatz map. For a start $n$, consider positive integers $s,r$ satisfying
--   $$
--   2^r,16cdot4^sle3^{r+2},
--   qquad
--   3^{r+3}mid 16cdot4^s(3n+1)-10 .
--   $$
--
--   Suppose $n$ is odd and there is at least one pair $(s,r)$ satisfying these conditions. Prove that a smaller positive start shares an ordinary Collatz iterate with $n$.
--
--   The desired conclusion is
--   $$
--   \exists k,a,b\in\mathbb N,\qquad 0<k<n,\qquad C^a(n)=C^b(k).
--   $$
--
--   The dyadic parameter $s$ determines a relay on the doubling ray above the first shortcut iterate of $n$. The other parameter controls the initial run from the smaller start.
-- source:
--   Sublemma of https://prove2.me/theorems/a817007c-cf46-5f67-813b-951301d0b33f. Extends the first-shortcut doubling-ray construction used in the sixfold cap analysis.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_smaller_merger_from_variable_dyadic_relay (n : ℕ) (hodd : n%2=1)
    (h : ∃ s r : ℕ, 0<s ∧ 0<r ∧ 2^r*(16*4^s)≤3^(r+2) ∧
      3^(r+3) ∣ 16*4^s*(3*n+1)-10) :
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k := by
  sorry
