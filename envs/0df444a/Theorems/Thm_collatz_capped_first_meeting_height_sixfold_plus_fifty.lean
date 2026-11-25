-- Prove2me | Theorems.Thm_collatz_capped_first_meeting_height_sixfold_plus_fifty
-- name    : collatz_capped_first_meeting_height_sixfold_plus_fifty
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T20:32:22.011895+00:00
-- url     : https://prove2.me/theorems/21b3d2d3-cdbc-4b46-aba2-c39c7d605b9b
-- title:
--   A capped Collatz merger must reach 6n+50 under the remaining visitor exclusions
-- statement:
--   Let $C$ be the ordinary Collatz map and let $S(x)=x/2$ for even $x$ and $S(x)=(3x+1)/2$ for odd $x$. For an exclusive cap $H$, join $x$ and $S(x)$ by an undirected edge when both values are strictly below $H$.
--
--   Suppose $32\le n<H$, $n\equiv15\pmod{16}$ and $0<k<n$. Assume the following:
--
--   - $C^a(n)\ge n$ for every $a\ge0$.
--   - No $q$ with $0<q<n$ has $C^t(q)=C^2(n)$ for any $t\ge0$.
--   - No odd $q$ with $0<q<n$ has $C^2(q)=C^a(n)$ for any $a\ge0$.
--
--   Prove that connectivity of $n$ and $k$ in the capped graph implies $6n+50<H$.
-- source:
--   Auxiliary for https://prove2.me/theorems/1fc58cdc-18fd-5655-a11a-ef1ffb8b1e18. The first-touch parent argument uses Section 4 of https://rstation.ai/problems/collatz/papers/213. The visit exclusions and the three nearby odd starts give the stated additive refinement.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Logic.Relation

theorem collatz_capped_first_meeting_height_sixfold_plus_fifty (H n k : ℕ)
    (hnH : n<H) (hlarge : 32≤n) (hclass : n%16=15)
    (hstay : ∀ a : ℕ, n≤collatzStep^[a] n)
    (hno : ¬∃ q t : ℕ, 0<q ∧ q<n ∧ collatzStep^[t] q=collatzStep^[2] n)
    (hpair : ∀ q a : ℕ, 0<q → q<n → q%2=1 → collatzStep^[2] q≠collatzStep^[a] n)
    (hk : 0<k) (hkn : k<n) :
    let shortcut : ℕ → ℕ := fun x => if x%2=0 then x/2 else (3*x+1)/2
    Relation.EqvGen (fun x y : ℕ => x<H ∧ y<H ∧ shortcut x=y) n k → 6*n+50<H := by
  sorry
