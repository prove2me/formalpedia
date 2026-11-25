-- Prove2me | Theorems.Thm_collatz_mergers_lift_at_independent_shortcut_clocks
-- name    : collatz_mergers_lift_at_independent_shortcut_clocks
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-25T21:13:48.796798+00:00
-- url     : https://prove2.me/theorems/59c8a136-4a85-4c2b-acb6-7c460ac397a5
-- title:
--   Lifting Collatz mergers at independent shortcut clocks
-- statement:
--   Let $C$ be the ordinary Collatz map, and let $S(x)=x/2$ for even $x$ and $S(x)=(3x+1)/2$ for odd $x$. Choose shortcut clocks $a,b$ and positive multipliers $u,v$. Put $P=2^a u$, $Q=2^b v$, and let $r$ be the least nonnegative residue of $n$ modulo $P$. An independent-clock certificate is a positive integer $s$ with
--   $$
--   s<r,\qquad Q\le P,\qquad S^a(r)=S^b(s),\qquad S^a(P+r)=S^b(Q+s).
--   $$
--
--   Prove that the certificate gives a smaller positive start sharing an ordinary Collatz iterate with $n$.
--   $$
--   \exists k,i,j\in\mathbb N,\qquad 0<k<n,\quad C^i(n)=C^j(k).
--   $$
--   The two widths allow the clocks and the input slopes to differ. The entire progression has the claimed merger, with the constructed smaller start $Q\lfloor n/P\rfloor+s$.
-- source:
--   Auxiliary to https://prove2.me/theorems/263f2e14-9fb8-4045-a502-459ebaa9ea8b. Uses affine shortcut lifts with separate widths and multipliers.

import Definitions.Def_collatzStepMap
import Mathlib.Logic.Function.Iterate

theorem collatz_mergers_lift_at_independent_shortcut_clocks (n a b u v s : ℕ) :
    let S : ℕ → ℕ := fun x => if x%2=0 then x/2 else (3*x+1)/2
    let P := 2^a*u
    let Q := 2^b*v
    let r := n%P
    (0<s ∧ s<r ∧ Q≤P ∧ S^[a] r=S^[b] s ∧ S^[a] (P+r)=S^[b] (Q+s)) →
    ∃ k i j : ℕ, 0<k ∧ k<n ∧ collatzStep^[i] n=collatzStep^[j] k := by
  sorry
