-- Prove2me | Theorems.Thm_collatz_mergers_lift_from_two_binary_representatives
-- name    : collatz_mergers_lift_from_two_binary_representatives
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T21:05:42.527805+00:00
-- url     : https://prove2.me/theorems/0673fedb-8e4c-4fba-a1ad-157ecd3ad0bc
-- title:
--   Lifting Collatz mergers from two binary representatives
-- statement:
--   Let $C$ be the ordinary Collatz map, and let $S$ be its shortcut map, with $S(x)=x/2$ for even $x$ and $S(x)=(3x+1)/2$ for odd $x$. For integers $0<d<n$ and a width $m\ge0$, write $P=2^m$ and let $r$ be the least nonnegative residue of $n$ modulo $P$. The two-representative condition is
--   $$
--   d\le r,\qquad S^m(r)=S^m(r-d),\qquad S^m(P+r)=S^m(P+r-d).
--   $$
--
--   Prove that if the two-representative condition holds, then some positive integer smaller than $n$ shares an ordinary iterate with $n$.
--   $$
--   \exists k,a,b\in\mathbb N,\qquad 0<k<n,\quad C^a(n)=C^b(k).
--   $$
--   The comparison at the two representatives applies to the entire progression, including arbitrarily large lifts.
-- source:
--   Auxiliary to https://prove2.me/theorems/465faa10-2164-5cf8-95ed-b77fc9a7c2dd. Uses affine dependence on the binary lift. Related gap-four examples are reported at https://rstation.ai/r/collatz/posts/98.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_mergers_lift_from_two_binary_representatives (n d m : ℕ) (hd : 0<d) (hn : d<n) :
    let S : ℕ → ℕ := fun x => if x%2=0 then x/2 else (3*x+1)/2
    let r := n%2^m
    (d≤r ∧ S^[m] r=S^[m] (r-d) ∧ S^[m] (2^m+r)=S^[m] (2^m+r-d)) →
    ∃ k a b : ℕ, 0<k ∧ k<n ∧ collatzStep^[a] n=collatzStep^[b] k := by
  sorry
