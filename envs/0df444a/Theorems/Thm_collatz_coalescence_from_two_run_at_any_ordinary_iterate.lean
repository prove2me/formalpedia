-- Prove2me | Theorems.Thm_collatz_coalescence_from_two_run_at_any_ordinary_iterate
-- name    : collatz_coalescence_from_two_run_at_any_ordinary_iterate
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T19:22:39.760802+00:00
-- url     : https://prove2.me/theorems/23861851-bf9c-46bb-b5ca-3a429c228915
-- title:
--   A smaller Collatz merger from a two-run visitor at any ordinary iterate
-- statement:
--   Let $C$ be the ordinary Collatz map and let $n$ be a positive integer. For nonnegative integers $t,e,h,d$, set
--   $$
--   y=C^t(n),\qquad z=2^e y+1.
--   $$
--   When $3^h$ divides $z$, define
--   $$
--   x=2^h z/3^h-1,\qquad w=2^d x+1,\qquad
--   r=v_3(w),\qquad k_{t,e,h,d}=2^r w/3^r-1 .
--   $$
--
--   Suppose there are $t,e,h,d$ with $3^h$ dividing $z$ and $k_{t,e,h,d}<n$. Prove that a smaller positive start meets the orbit of $n$.
--
--   The desired merger is
--   $$
--   \exists k,a,b\in\mathbb N,\qquad 0<k<n,\qquad C^a(n)=C^b(k).
--   $$
--
--   The two blocks of paired odd steps and halvings can meet the original orbit at any ordinary iterate.
-- source:
--   Sublemma of https://prove2.me/theorems/bd7428ba-1c9e-46c8-bb7a-62838850bb8c.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic

theorem collatz_coalescence_from_two_run_at_any_ordinary_iterate (n : ℕ) (hn : 0<n)
    (h : ∃ t e h d : ℕ,
      let y := collatzStep^[t] n
      let z := 2^e*y+1
      let x := 2^h*(z/3^h)-1
      let w := 2^d*x+1
      let r := w.factorization 3
      3^h ∣ z ∧ 2^r*(w/3^r)-1<n) :
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k := by
  sorry
