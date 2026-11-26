-- Prove2me | Theorems.Thm_collatz_merger_reciprocal_and_height_after_both_lift_exclusions
-- name    : collatz_merger_reciprocal_and_height_after_both_lift_exclusions
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T04:09:47.73133+00:00
-- url     : https://prove2.me/theorems/71081bea-c531-4f12-8840-ecb617f892c9
-- title:
--   Reciprocal and height constraints after both Collatz lift exclusions
-- statement:
--   Let $C$ be the ordinary Collatz map and let $S$ be the shortcut map $x\mapsto x/2$ for even $x$ and $x\mapsto(3x+1)/2$ for odd $x$. Let $o(t,x)$ count odd departures along the first $t$ shortcut steps. Define the rational correction
--   $$R(t,x)=\sum_{0\le i<t,\ S^i(x)\text{ odd}}\frac{1}{3S^i(x)+1}.$$
--
--   Fix an odd $n\ge1000$ whose ordinary orbit stays at least $n$. Assume $n$ has neither of the following two affine merger certificates.
--
--   - A same-clock certificate has $0<d<n$ and width $m$. With $r=n\bmod 2^m$, it has $d\le r$, $S^m(r)=S^m(r-d)$, and $S^m(2^m+r)=S^m(2^m+r-d)$.
--   - An independent-clock certificate has distinct clocks $c,d$ and positive $u,v,s$. With $P=2^c u$, $Q=2^d v$ and $r=n\bmod P$, it has $s<r$, $Q\le P$, $S^c(r)=S^d(s)$, and $S^c(P+r)=S^d(Q+s)$.
--
--   Suppose $0<k<n$ and $S^a(n)=S^b(k)$. Prove that at least one of the following holds.
--
--   - The original normalized multiplier is larger, $2^a3^{o(b,k)}<2^b3^{o(a,n)}$, and $R(b,k)>1-k/n$.
--   - The clocks are equal, $k$ is odd, $2n\le3k+1$, and $S^i(n)\ge16n$ for some $i<a$.
-- source:
--   Auxiliary to the merger frontier at https://prove2.me/theorems/6addc3e8-67b2-4e46-89d0-51db65db2c7b. Extends the gain comparison at https://prove2.me/theorems/cb6e80b5-d0d4-4ed6-89b4-596bc96413ce by bounding the actual trajectory correction.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Rat.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem collatz_merger_reciprocal_and_height_after_both_lift_exclusions (n k a b : ℕ) (hn : 1000 ≤ n) (hodd : n % 2 = 1)
    (hstay : ∀ t : ℕ, n ≤ collatzStep^[t] n) (hk : 0 < k) (hkn : k < n) :
    let S : ℕ → ℕ := fun x => if x % 2 = 0 then x / 2 else (3*x+1) / 2
    let odd : ℕ → ℕ → ℕ := fun t x => ((List.range t).map (fun i => (S^[i] x) % 2)).sum
    let R : ℕ → ℕ → ℚ := fun t x => (Finset.range t).sum fun i =>
      if (S^[i] x) % 2 = 0 then 0 else (3*(S^[i] x : ℕ)+1 : ℚ)⁻¹
    let equalLift := ∃ d m : ℕ, 0 < d ∧ d < n ∧
      let r := n % 2^m
      d ≤ r ∧ S^[m] r = S^[m] (r-d) ∧ S^[m] (2^m+r) = S^[m] (2^m+r-d)
    let independentLift := ∃ c d u v s : ℕ, 0 < u ∧ 0 < v ∧ c ≠ d ∧
      let P := 2^c*u
      let Q := 2^d*v
      let r := n % P
      0 < s ∧ s < r ∧ Q ≤ P ∧ S^[c] r = S^[d] s ∧ S^[c] (P+r) = S^[d] (Q+s)
    ¬equalLift → ¬independentLift → S^[a] n = S^[b] k →
      (2^a*3^odd b k < 2^b*3^odd a n ∧ 1-(k:ℚ)/n < R b k) ∨
      (a = b ∧ k % 2 = 1 ∧ 2*n ≤ 3*k+1 ∧ ∃ i < a, 16*n ≤ S^[i] n) := by
  sorry
