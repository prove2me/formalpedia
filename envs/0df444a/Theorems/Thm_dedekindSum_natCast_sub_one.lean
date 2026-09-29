-- Prove2me | Theorems.Thm_dedekindSum_natCast_sub_one
-- name    : dedekindSum_natCast_sub_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/00412770-7e7c-5f82-b5e2-c4ab5c5ba4c9
-- title:
--   Oddness of the Dedekind sum: s(k-1,k)=-s(1,k)
-- statement:
--   For a natural number $k$, write $\mathrm{dedekindSaw}(x)=0$ if the fractional part of the rational $x$ vanishes and $\mathrm{dedekindSaw}(x)=\{x\}-\tfrac12$ otherwise, and for $h\in\mathbb{Z}$ set $$s(h,k)=\sum_{r=0}^{k-1}\mathrm{dedekindSaw}\!\left(\frac{r}{k}\right)\,\mathrm{dedekindSaw}\!\left(\frac{hr}{k}\right),$$ the sum being taken over $r$ in the range $0,\dots,k-1$ and computed in $\mathbb{Q}$. The theorem asserts, for every natural number $k$ with no further hypotheses, the identity $$s(k-1,k)=-s(1,k),$$ where the first argument is the integer $(k:\mathbb{Z})-1$, so that for $k=0$ it is $-1$ and both sides are the empty sum $0$. Thus it is the special case at $h=1$ of the combination of periodicity of $s(h,k)$ in $h$ modulo $k$ and oddness $s(-h,k)=-s(h,k)$, stated here directly for the pair $(k-1,k)$ rather than through those two general properties.
--
--   This is the classical evaluation $s(k-1,k)=-s(1,k)$ for Dedekind sums, reflecting their periodicity in the first argument and their oddness under $h\mapsto -h$. It is used in the computations of the Rademacher function $\Phi$ at particular levels, where the witnesses for residues $49$, $61$ and $109$ modulo $120$ invoke it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_dedekindSum_natCast_sub_one.lean

import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem dedekindSum_natCast_sub_one (k : ℕ) : dedekindSum ((k : ℤ) - 1) k = -dedekindSum 1 k := by sorry
