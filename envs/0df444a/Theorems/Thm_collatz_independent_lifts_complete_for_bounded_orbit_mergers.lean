-- Prove2me | Theorems.Thm_collatz_independent_lifts_complete_for_bounded_orbit_mergers
-- name    : collatz_independent_lifts_complete_for_bounded_orbit_mergers
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T02:50:57.854789+00:00
-- url     : https://prove2.me/theorems/eb8411db-57c0-445c-94c0-a30ec2b8d2ec
-- title:
--   Independent-clock certificates characterize mergers of bounded Collatz orbits
-- statement:
--   Let $C$ be the ordinary Collatz map and $S$ its shortcut, with $S(x)=x/2$ for even $x$ and $S(x)=(3x+1)/2$ for odd $x$. A smaller merger of $n$ means that $C^i(n)=C^j(k)$ for some $0<k<n$ and clocks $i,j$.
--
--   An independent-clock certificate for $n$ consists of unequal shortcut clocks $a,b$, positive multipliers $u,v$ and a positive integer $s$. Write $P=2^a u$, $Q=2^b v$, and $r=n\bmod P$. The certificate satisfies
--   $$
--   s<r,\qquad Q\le P,\qquad S^a(r)=S^b(s),\qquad S^a(P+r)=S^b(Q+s).
--   $$
--
--   Prove that for a bounded ordinary orbit a smaller merger exists exactly when an independent-clock certificate exists. Also prove that if a smaller merger exists and there is no such certificate, the original orbit eventually stays above every height:
--   $$
--   \forall H\in\mathbb N\;\exists T\in\mathbb N\;\forall t\ge T,\qquad C^t(n)>H.
--   $$
--   This relates the certificate exclusion to the bounded and escaping cases of the merger problem.
-- source:
--   Auxiliary to https://prove2.me/theorems/6addc3e8-67b2-4e46-89d0-51db65db2c7b. Uses affine shortcut lifting and the strict contraction of the normalized multiplier around a return.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_independent_lifts_complete_for_bounded_orbit_mergers (n : ℕ) :
    let S : ℕ → ℕ := fun x => if x%2=0 then x/2 else (3*x+1)/2
    let lift := ∃ a b u v s : ℕ, 0<u ∧ 0<v ∧ a≠b ∧
      let P := 2^a*u
      let Q := 2^b*v
      let r := n%P
      0<s ∧ s<r ∧ Q≤P ∧ S^[a] r=S^[b] s ∧ S^[a] (P+r)=S^[b] (Q+s)
    let merger := ∃ k i j : ℕ, 0<k ∧ k<n ∧ collatzStep^[i] n=collatzStep^[j] k
    (∀ H : ℕ, (∀ t : ℕ, collatzStep^[t] n≤H) → (merger ↔ lift)) ∧
    (merger → lift ∨ (∀ H : ℕ, ∃ T : ℕ, ∀ t : ℕ, T≤t → H<collatzStep^[t] n)) := by
  sorry
