-- Prove2me | Theorems.Thm_syracuse_nontrivial_period_farey_coordinates
-- name    : syracuse_nontrivial_period_farey_coordinates
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T10:09:51.013521+00:00
-- url     : https://prove2.me/theorems/74014f79-4ad3-4245-bd3d-22fe785ef4f4
-- title:
--   Positive Farey coordinates for a nontrivial Syracuse return time
-- statement:
--   If $m>0$, $m\ne1$, and $T^p(m)=m$ for $p>0$, write $K=\sum_{i<p}v_2(3T^i(m)+1)$. There are positive integers $a,b$ such that $(p,K)=a(665,1054)+b(10946,17349)$, with $2a<15b$ and $2b\le13a$. Thus $p\ge11611$. In the range $7621\le p\le100000$, these constraints leave 205 candidate lengths, versus 244 under the earlier three-entry estimate.
-- source:
--   Determinant-one change of basis for the dyadic comparison theorem syracuse_nontrivial_cycle_dyadic_exponent_bound and the strict cycle power gap.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem syracuse_nontrivial_period_farey_coordinates (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) (hne : m ≠ 1) :
    let K := ∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      p = 665*a + 10946*b ∧ K = 1054*a + 17349*b ∧ 2*a < 15*b ∧ 2*b ≤ 13*a := by sorry
