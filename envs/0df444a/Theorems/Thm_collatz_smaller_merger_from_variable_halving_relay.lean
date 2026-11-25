-- Prove2me | Theorems.Thm_collatz_smaller_merger_from_variable_halving_relay
-- name    : collatz_smaller_merger_from_variable_halving_relay
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:12:15.940128+00:00
-- url     : https://prove2.me/theorems/be3d9b80-600c-4b15-bb9d-c9b565dff5a9
-- title:
--   Smaller Collatz mergers with two independently variable halving counts
-- statement:
--   Let $C$ be the ordinary Collatz map. For a start $n$, consider a nonnegative integer $s$, a positive integer $r$, and halving counts $a,bge2$. Put
--   $$
--   P=2^{a+b}4^s,qquad D=2^{a+b}+3cdot2^b .
--   $$
--   The two arithmetic conditions are
--   $$
--   2^r Ple3^{r+2},qquad
--   3^{r+3}mid P(3n+1)+18-D .
--   $$
--
--   Suppose $n$ is odd and some choice of the four parameters satisfies both conditions. Prove that a smaller positive start shares an ordinary Collatz iterate with $n$.
--
--   The desired conclusion is
--   $$
--   \exists k,i,j\in\mathbb N,\qquad 0<k<n,\qquad C^i(n)=C^j(k).
--   $$
--
--   The two intervening halving counts may differ. The meeting occurs at ordinary time two for $n$.
-- source:
--   Sublemma of https://prove2.me/theorems/a1df4edc-8b63-51f9-989f-fd985c8c12bc. Extends the preceding variable dyadic relay by allowing the two intervening halving counts to vary independently.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_smaller_merger_from_variable_halving_relay (n : ℕ) (hodd : n%2=1)
    (h : ∃ s r a b : ℕ, 0<r ∧ 2≤a ∧ 2≤b ∧
      2^r*(2^(a+b)*4^s)≤3^(r+2) ∧
      3^(r+3) ∣ 2^(a+b)*4^s*(3*n+1)+18-(2^(a+b)+3*2^b)) :
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k := by
  sorry
