-- Prove2me | Theorems.Thm_collatz_smaller_mergers_through_first_odd_run_exit_exact
-- name    : collatz_smaller_mergers_through_first_odd_run_exit_exact
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:39:55.771635+00:00
-- url     : https://prove2.me/theorems/835d2b81-e941-5f4f-a8db-581ad9efb8b9
-- title:
--   Exact affine criterion for mergers through the first odd-run exit
-- statement:
--   Let $C$ be the ordinary Collatz map. For a positive start $n$, set $r=v_2(n+1)$ and $W=3^r(n+1)/2^r-1$. Set $s=v_2(W)$, $T=2r+s$, and $y=W/2^s$. Thus $y$ is the odd endpoint obtained after the initial succession of odd steps paired with one halving each, followed by all remaining halvings of $W$.
--
--   For a finite list $v$ of positive halving counts, write $E=\sum v$, $L=|v|$, and define its offset by $B([])=0$ and $B(a::u)=3^{|u|}+2^aB(u)$. The affine condition is that a finite list satisfies
--   $$
--   z=2^E y-B(v)>0,\qquad 3^L\mid z,\qquad z<3^L n .
--   $$
--
--   Prove that the affine condition is equivalent to the existence of a smaller positive starting value whose orbit meets that of $n$ at some original clock at most $T$. The clock on the smaller-start orbit is unrestricted.
--   $$
--   \exists k,a,b\in\mathbb{N},\qquad 0<k<n,\quad a\le T,\quad C^a(n)=C^b(k).
--   $$
-- source:
--   Auxiliary to https://prove2.me/theorems/1fc58cdc-18fd-5655-a11a-ef1ffb8b1e18. Uses an affine word to encode every visitor to the odd endpoint and forwards earlier meetings to that endpoint.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Nat.Factorization.Basic

theorem collatz_smaller_mergers_through_first_odd_run_exit_exact (n : ℕ) (hn : 0<n) :
    let r := (n+1).factorization 2
    let w := 3^r*((n+1)/2^r)-1
    let s := w.factorization 2
    (∃ k a b : ℕ, 0<k ∧ k<n ∧ a≤s+2*r ∧ collatzStep^[a] n=collatzStep^[b] k) ↔
    (∃ v : List ℕ, (∀ a∈v, 0<a) ∧
      let B := (v.foldr (fun a (p : ℕ × ℕ) => (p.1+1,3^p.1+2^a*p.2)) (0,0)).2
      let z := 2^v.sum*(w/2^s)-B
      0<z ∧ 3^v.length ∣ z ∧ z<3^v.length*n) := by
  sorry
