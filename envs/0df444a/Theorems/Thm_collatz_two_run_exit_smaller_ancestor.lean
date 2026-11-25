-- Prove2me | Theorems.Thm_collatz_two_run_exit_smaller_ancestor
-- name    : collatz_two_run_exit_smaller_ancestor
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T18:31:46.278433+00:00
-- url     : https://prove2.me/theorems/d4d84904-742f-506d-9aa7-c281ccc7403b
-- title:
--   A smaller Collatz ancestor at a two-run exit
-- statement:
--   Let $C$ be the ordinary Collatz map. Suppose $Lge4$, $q,Q>0$, and $Hge0$. Set $n=2^Lq-1$ and $W=3^H Q$, and suppose $3^Lq+1=2^{H+1}Q$. Let $s,r$ be natural numbers satisfying
--   $$
--   1le s,quad rle H,quad 2^smid W-1,quad
--   2^{s-1}equiv1pmod{3^r},quad
--   2^r(W+2^{s-1}-1)le 3^r2^{s-1}n .
--   $$
--
--
--   Then there is a smaller positive start whose orbit meets the orbit of $n$.
--   $$
--   exists k,a,binmathbb N,qquad 0<k<n,qquad C^a(n)=C^b(k).
--   $$
--
--   The comparison is with the original start, including when the common exit is above $n$.
-- source:
--   New arithmetic case in the residual https://prove2.me/theorems/b4e49a00-b11f-5218-8898-364b587bdc78, using the two-run identities of https://prove2.me/theorems/a1e61e1e-88b7-5c58-aff2-a3fddfe48535.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_two_run_exit_smaller_ancestor
    (L q H Q s r : ℕ) (hL : 4 ≤ L) (hq : 0 < q) (hQ : 0 < Q)
    (hbetween : 3^L*q+1 = 2^(H+1)*Q) (hs : 1 ≤ s) (hr : r ≤ H)
    (hdiv : 2^s ∣ 3^H*Q-1) (hres : 2^(s-1) % 3^r = 1)
    (hmargin : 2^r*(3^H*Q+2^(s-1)-1) ≤ 3^r*2^(s-1)*(2^L*q-1)) :
    ∃ k a b : ℕ, 0 < k ∧ k < 2^L*q-1 ∧
      collatzStep^[a] (2^L*q-1) = collatzStep^[b] k := by sorry
