-- Prove2me | Theorems.Thm_collatz_coalescence_from_one_run_at_any_ordinary_iterate
-- name    : collatz_coalescence_from_one_run_at_any_ordinary_iterate
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T19:16:50.048726+00:00
-- url     : https://prove2.me/theorems/9527c568-d321-4ce6-902f-ed79c397a3e8
-- title:
--   A smaller Collatz merger from a one-run visitor at any ordinary iterate
-- statement:
--   Let $C$ be the ordinary Collatz map. For $t,e\in\mathbb N$ and a positive starting value $n$, set
--   $$
--   y=C^t(n),\qquad z=2^e y+1,\qquad r=v_3(z),\qquad k_{t,e}=2^r z/3^r-1 .
--   $$
--
--   Suppose there are $t,e$ for which $k_{t,e}<n$. Prove that the orbit of $n$ meets the orbit of a smaller positive start.
--
--   The desired orbit merger is
--   $$
--   \exists k,a,b\in\mathbb N,\qquad 0<k<n,\qquad C^a(n)=C^b(k).
--   $$
--
--   The meeting value may be any ordinary iterate, including a point inside an odd run of the original trajectory.
-- source:
--   Sublemma of https://prove2.me/theorems/bec8f45c-2b85-547c-a604-921f351ea6a1.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic

theorem collatz_coalescence_from_one_run_at_any_ordinary_iterate (n : ℕ) (hn : 0<n)
    (h : ∃ t e : ℕ,
      let y := collatzStep^[t] n
      let z := 2^e*y+1
      let r := z.factorization 3
      2^r*(z/3^r)-1<n) :
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k := by
  sorry
