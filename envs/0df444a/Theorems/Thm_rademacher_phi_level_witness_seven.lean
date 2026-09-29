-- Prove2me | Theorems.Thm_rademacher_phi_level_witness_seven
-- name    : rademacher_phi_level_witness_seven
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/106c3625-431e-5aec-9dfc-13d1e8d93878
-- title:
--   Dedekind-sum witness for levels ℓ≡ 7(mod 12)
-- statement:
--   For every natural number $j$, write $\ell = 12j+7$, $a = 3j+2$ and $d = 4$. Here $s(h,k) = \sum_{r=0}^{k-1}\big(\!\!\big(\tfrac{r}{k}\big)\!\!\big)\big(\!\!\big(\tfrac{hr}{k}\big)\!\!\big)$ is [`dedekindSum`](def/NumberTheory_DedekindSum.html#L73), built from the sawtooth $\big(\!\!\big(x\big)\!\!\big)$ which is $0$ when the fractional part of $x$ vanishes and $\{x\} - \tfrac12$ otherwise. The assertion is a conjunction of two statements about rationals and naturals. First, the identity $$12\left(\frac{(a+d)(1-\ell)}{12\,\ell} + s(4,1) - s(4,\ell)\right) = \gcd(\ell - 1,\,12)\cdot\big(-(j+1)\big),$$ where $\ell-1$ is formed by truncated subtraction in $\mathbb{N}$, i.e. equals $12j+6$, and the right-hand factor is the image of the integer $-(j+1)$ in $\mathbb{Q}$. Second, the natural numbers $|-(j+1)| = j+1$ and $(\ell-1)/\gcd(\ell-1,12)$, the quotient taken in $\mathbb{N}$, are coprime. Since $\gcd(12j+6,12) = 6$, the two clauses say concretely that the left-hand side equals $-6(j+1)$ and that $j+1$ is coprime to $2j+1$.
--
--   The bracketed expression is the difference of values of Rademacher's $\Phi$-function attached to the eta multiplier system, evaluated at a matrix of determinant one with lower row $(\ell,4)$ and upper left entry $3j+2$; the theorem records its exact value together with the coprimality needed to realise it as a generator. It supplies the numerical witness used by [`ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_seven`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_seven) for levels congruent to $7$ modulo $12$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_rademacher_phi_level_witness_seven.lean

import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem rademacher_phi_level_witness_seven (j : ℕ) : 12 * ((((3 * j + 2 : ℕ) + 4 : ℤ) : ℚ) * (1 - ((12 * j + 7 : ℕ) : ℚ)) / (12 * ((12 * j + 7 : ℕ) : ℚ)) + dedekindSum 4 1 - dedekindSum 4 (12 * j + 7)) = ((Nat.gcd ((12 * j + 7) - 1) 12 : ℕ) : ℚ) * (-((j : ℤ) + 1)) ∧ Nat.Coprime (Int.natAbs (-((j : ℤ) + 1))) (((12 * j + 7) - 1) / Nat.gcd ((12 * j + 7) - 1) 12) := by sorry
