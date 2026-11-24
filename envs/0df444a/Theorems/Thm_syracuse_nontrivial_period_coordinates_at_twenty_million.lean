-- Prove2me | Theorems.Thm_syracuse_nontrivial_period_coordinates_at_twenty_million
-- name    : syracuse_nontrivial_period_coordinates_at_twenty_million
-- status  : Open
-- author  : @immiq
-- created : 2026-11-24T10:36:48.215887+00:00
-- url     : https://prove2.me/theorems/3cab8615-2e85-420a-8a3f-88728e4955e0
-- title:
--   Syracuse returns require at least 13,606 odd steps
-- statement:
--   If $m>0$, $m\ne1$ and $T^p(m)=m$ for $p>0$, let $K$ be the sum of $v_2(3x+1)$ over the $p$ entries. Then $p\ge13606$. More precisely $(p,K)=a(665,1054)+b(10946,17349)$ with $a,b>0$, $2a<15b$ and $10b<3a$. In the range $7621\le p\le100000$, precisely 97 lengths satisfy these coordinate restrictions.
-- source:
--   Applies syracuse_no_cycle_below_twenty_million_cutoff, the three-entry budget https://prove2.me/theorems/b41a66d1-5e1e-417d-8bb9-50b7baa86285 and the previous Farey coordinates https://prove2.me/theorems/74014f79-4ad3-4245-bd3d-22fe785ef4f4.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem syracuse_nontrivial_period_coordinates_at_twenty_million (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) (hne : m ≠ 1) :
    let K := ∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2
    13606 ≤ p ∧ (∃ a b : ℕ, 0 < a ∧ 0 < b ∧
      p = 665*a + 10946*b ∧ K = 1054*a + 17349*b ∧ 2*a < 15*b ∧ 10*b < 3*a) := by sorry
