-- Prove2me | Theorems.Thm_dedekindSum_one_left
-- name    : dedekindSum_one_left
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/7f4870ed-e064-5f49-9ff6-08832a3f977c
-- title:
--   Closed form s(1,k)=(k-1)(k-2)/(12k)
-- statement:
--   For every natural number $k$, the Dedekind sum with first argument the integer $1$ and second argument $k$ equals $((k-1)(k-2))/(12k)$ in $\mathbb{Q}$, where $k$ is coerced to a rational. Here the Dedekind sum is defined by $$\mathrm{dedekindSum}(h,k)=\sum_{r=0}^{k-1}\mathrm{dedekindSaw}\!\left(\frac{r}{k}\right)\mathrm{dedekindSaw}\!\left(\frac{hr}{k}\right),$$ the index $r$ running over `Finset.range k`, and the sawtooth function is $\mathrm{dedekindSaw}(x)=0$ when the fractional part of $x$ vanishes and $\mathrm{dedekindSaw}(x)=\{x\}-\tfrac12$ otherwise. Thus for $h=1$ the assertion is that $\sum_{r=0}^{k-1}\mathrm{dedekindSaw}(r/k)^2=((k-1)(k-2))/(12k)$; the term $r=0$ contributes nothing, and for $1\le r\le k-1$ the summand is $(r/k-\tfrac12)^2$. No hypothesis is imposed on $k$: for $k\ge1$ the denominator $12k$ is nonzero and the identity is the classical closed form, while for $k=0$ both sides are $0$, the left side being an empty sum and the right side using the convention $x/0=0$ in $\mathbb{Q}$.
--
--   This is the standard evaluation of the Dedekind sum $s(1,k)$, the base case from which the values of $s(h,k)$ at small $h$ are obtained via reciprocity. It is used in the explicit computations of the Rademacher function $\Phi$ on congruence classes modulo $120$, such as [`rademacher_phi_level_witness_mod_oneTwenty_eq_one`](thm.html#rademacher_phi_level_witness_mod_oneTwenty_eq_one) and [`rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine`](thm.html#rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_dedekindSum_one_left.lean

import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem dedekindSum_one_left (k : ℕ) : dedekindSum 1 k = ((k : ℚ) - 1) * ((k : ℚ) - 2) / (12 * k) := by sorry
