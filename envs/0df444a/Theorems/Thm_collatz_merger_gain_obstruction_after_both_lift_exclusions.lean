-- Prove2me | Theorems.Thm_collatz_merger_gain_obstruction_after_both_lift_exclusions
-- name    : collatz_merger_gain_obstruction_after_both_lift_exclusions
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T03:00:50.254285+00:00
-- url     : https://prove2.me/theorems/cb6e80b5-d0d4-4ed6-89b4-596bc96413ce
-- title:
--   Gain and odd-step constraints after both Collatz lift exclusions
-- statement:
--   Let $C$ be the ordinary Collatz map, and let $S(x)=x/2$ for even $x$ and $S(x)=(3x+1)/2$ for odd $x$. Write $o(t,x)$ for the number of odd states before the first $t$ shortcut steps from $x$. Its normalized multiplier is $3^{o(t,x)}/2^t$.
--
--   Fix $n\ge3$ whose ordinary orbit stays at least $n$. Assume $n$ has neither kind of affine certificate:
--
--   - A same-clock certificate consists of $0<d<n$ and a width $m$, with $P=2^m$, $r=n\bmod P$, $d\le r$, $S^m(r)=S^m(r-d)$, and $S^m(P+r)=S^m(P+r-d)$.
--   - An independent-clock certificate consists of unequal clocks $c,d$, positive multipliers $u,v$, and $s>0$. With $P=2^c u$, $Q=2^d v$, and $r=n\bmod P$, it satisfies $s<r$, $Q\le P$, $S^c(r)=S^d(s)$, and $S^c(P+r)=S^d(Q+s)$.
--
--   Suppose $0<k<n$ and $S^a(n)=S^b(k)$. Prove that one of the following holds.
--
--   - The original normalized multiplier is strictly larger, and if every state of the visitor through clock $b$ is at least $k$, then
--     $$3k(n-k)<n\,o(b,k).$$
--   - The clocks are equal, $k$ is odd, $2n\le3k+1$, and the original path has more than $n$ odd steps: $n<o(a,n)$.
--
--   This bounds both possible forms of a meeting on the branch that excludes the two lifting certificates.
-- source:
--   Auxiliary to https://prove2.me/theorems/6addc3e8-67b2-4e46-89d0-51db65db2c7b. Uses the two affine lifting theorems and exact integer multiplicative estimates along the two paths.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_merger_gain_obstruction_after_both_lift_exclusions (n k a b : ℕ)
    (hn : 3≤n) (hstay : ∀ t : ℕ, n≤collatzStep^[t] n) (hk : 0<k) (hkn : k<n) :
    let S : ℕ → ℕ := fun x => if x%2=0 then x/2 else (3*x+1)/2
    let odd : ℕ → ℕ → ℕ := fun t x => ((List.range t).map (fun i => (S^[i] x)%2)).sum
    let equalLift := ∃ d m : ℕ, 0<d ∧ d<n ∧
      let r := n%2^m
      d≤r ∧ S^[m] r=S^[m] (r-d) ∧ S^[m] (2^m+r)=S^[m] (2^m+r-d)
    let independentLift := ∃ c d u v s : ℕ, 0<u ∧ 0<v ∧ c≠d ∧
      let P := 2^c*u
      let Q := 2^d*v
      let r := n%P
      0<s ∧ s<r ∧ Q≤P ∧ S^[c] r=S^[d] s ∧ S^[c] (P+r)=S^[d] (Q+s)
    ¬equalLift → ¬independentLift → S^[a] n=S^[b] k →
      (2^a*3^odd b k<2^b*3^odd a n ∧
        ((∀ i : ℕ, i≤b → k≤S^[i] k) → 3*k*(n-k)<odd b k*n)) ∨
      (a=b ∧ k%2=1 ∧ 2*n≤3*k+1 ∧ n<odd a n) := by
  sorry
