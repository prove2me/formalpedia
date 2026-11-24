-- Prove2me | Theorems.Thm_syracuse_nontrivial_cycle_dyadic_exponent_bound
-- name    : syracuse_nontrivial_cycle_dyadic_exponent_bound
-- status  : Proved
-- author  : @immiq
-- created : 2026-11-24T10:09:50.568913+00:00
-- url     : https://prove2.me/theorems/993eaf2f-ee56-4645-ace2-307046c3efcf
-- title:
--   A dyadic comparison bound for valuations on a nontrivial Syracuse cycle
-- statement:
--   Let $T$ send $m$ to the odd part of $3m+1$. If $m>0$, $m\ne1$, $p>0$, and $T^p(m)=m$, put $K=\sum_{i=0}^{p-1}v_2(3T^i(m)+1)$. Then $143628K\le227645p$. The bound uses a rounded dyadic comparison sequence and the verified exclusion of cycle entries below $2^{23}$.
-- source:
--   Dyadic upper comparison using the cutoff https://prove2.me/theorems/3200d4f9-6281-4ae0-b7a3-d564488a54d7 in the residual https://prove2.me/theorems/d1678ccb-a2e9-47ff-834f-b37b28d280f6.

import Definitions.Def_syracuseStep
import Mathlib.Logic.Function.Iterate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

theorem syracuse_nontrivial_cycle_dyadic_exponent_bound (m p : ℕ) (hm : 0 < m) (hp : 0 < p)
    (hcycle : syracuseStep^[p] m = m) (hne : m ≠ 1) :
    143628 * (∑ i ∈ Finset.range p, (3*syracuseStep^[i] m+1).factorization 2) ≤
      227645 * p := by sorry
