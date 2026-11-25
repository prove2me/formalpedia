-- Prove2me | Theorems.Thm_collatz_smaller_mergers_through_second_odd_run_exit_exact
-- name    : collatz_smaller_mergers_through_second_odd_run_exit_exact
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:57:47.299241+00:00
-- url     : https://prove2.me/theorems/5007aa48-f320-5a3a-a73d-6639e8954546
-- title:
--   Exact affine criterion for mergers through the second odd-run exit
-- statement:
--   Let $C$ be the ordinary Collatz map. For $x>0$, put
--   $$
--   r(x)=v_2(x+1),\qquad W(x)=3^{r(x)}(x+1)/2^{r(x)}-1,
--   $$
--   and let $s(x)=v_2(W(x))$, $J(x)=W(x)/2^{s(x)}$, and $D(x)=2r(x)+s(x)$. Thus $J(x)$ is the odd run exit that follows the initial $r(x)$ odd-step pairs and the remaining $s(x)$ halvings. For a start $n>0$, let $T=D(n)+D(J(n))$ and $y=J(J(n))$.
--
--   A finite list $v$ of positive halving counts has length $L$ and total $E$. Set $B([])=0$ and $B(a::u)=3^{|u|}+2^aB(u)$. Say the affine condition holds if some such list satisfies
--   $$
--   z=2^E y-B(v)>0,\qquad 3^L\mid z,\qquad z<3^L n .
--   $$
--
--   Prove that this affine condition is equivalent to the existence of a meeting at an original clock at or before the second run exit.
--   $$
--   \exists k,a,b\in\mathbb N,\qquad 0<k<n,\quad a\le T,\quad C^a(n)=C^b(k).
--   $$
--   The list length and the clock on the smaller-start orbit are unrestricted. The condition includes meetings during the intervening ordinary steps.
-- source:
--   Auxiliary to https://prove2.me/theorems/5b7d9a89-44c1-4773-99fa-a4c0ee992df8. Extends the exact odd-target affine criterion through both initial run exits.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic

theorem collatz_smaller_mergers_through_second_odd_run_exit_exact (n : ℕ) (hn : 0<n) :
    let runEnd : ℕ → ℕ := fun x =>
      let r := (x+1).factorization 2
      3^r*((x+1)/2^r)-1
    let jump : ℕ → ℕ := fun x =>
      let w := runEnd x
      w/2^(w.factorization 2)
    let duration : ℕ → ℕ := fun x => (runEnd x).factorization 2+2*((x+1).factorization 2)
    let T := duration n+duration (jump n)
    (∃ k a b : ℕ, 0<k ∧ k<n ∧ a≤T ∧ collatzStep^[a] n=collatzStep^[b] k) ↔
    (∃ v : List ℕ, (∀ a∈v, 0<a) ∧
      let y := jump (jump n)
      let B := (v.foldr (fun a (p : ℕ × ℕ) => (p.1+1,3^p.1+2^a*p.2)) (0,0)).2
      let z := 2^v.sum*y-B
      0<z ∧ 3^v.length ∣ z ∧ z<3^v.length*n) := by
  sorry
