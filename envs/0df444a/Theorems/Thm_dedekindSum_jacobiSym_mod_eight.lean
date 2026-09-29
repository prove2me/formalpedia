-- Prove2me | Theorems.Thm_dedekindSum_jacobiSym_mod_eight
-- name    : dedekindSum_jacobiSym_mod_eight
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/c30fdfd3-a298-5856-9384-46b8797a0574
-- title:
--   Dedekind's congruence modulo 8 for 12k s(h,k)
-- statement:
--   Let $h$ and $k$ be natural numbers, with $k$ odd and $h$ coprime to $k$. Here the Dedekind sum $s(h,k)$ is the rational number $\sum_{r=0}^{k-1} \big(\!\big(\tfrac{r}{k}\big)\!\big)\,\big(\!\big(\tfrac{hr}{k}\big)\!\big)$, where the sawtooth function $\big(\!\big(x\big)\!\big)$ is defined to be $0$ when the fractional part of $x$ vanishes and $\{x\} - \tfrac12$ otherwise; the arguments $r/k$ and $hr/k$ are formed in $\mathbb{Q}$ with $h$ viewed as an integer. The assertion is that there exists an integer $t$ with
--   $$12k\,s(h,k) = k + 1 - 2\left(\frac{h}{k}\right) + 8t$$
--   as an identity in $\mathbb{Q}$, where $\left(\frac{h}{k}\right)$ is the Jacobi symbol of $h$ modulo $k$, an integer cast into $\mathbb{Q}$. Thus $12k\,s(h,k)$ is in particular a rational integer for odd $k$, and it is congruent to $k + 1 - 2\left(\frac{h}{k}\right)$ modulo $8$. Note that oddness of $k$ forces $k \geq 1$, so no separate positivity hypothesis appears.
--
--   This is Dedekind's classical congruence linking Dedekind sums to the Jacobi symbol, the source of the quadratic-residue information carried by the Rademacher phase. It is used in the proof of [`ModularCurve.sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine), where a witness at prime level congruent to $1$ modulo $8$ must be a quadratic residue.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_dedekindSum_jacobiSym_mod_eight.lean

import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem dedekindSum_jacobiSym_mod_eight (h k : ℕ) (hk : Odd k) (hhk : Nat.Coprime h k) : ∃ t : ℤ, 12 * (k : ℚ) * dedekindSum h k = (k : ℚ) + 1 - 2 * ((jacobiSym h k : ℤ) : ℚ) + 8 * t := by sorry
