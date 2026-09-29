-- Prove2me | Theorems.Thm_rademacher_phi_level_congruence
-- name    : rademacher_phi_level_congruence
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/0ba12fc0-1fd4-56a5-ad81-86b6f9a7bba5
-- title:
--   Rademacher's congruence for Φ at level ℓ
-- statement:
--   Let $\ell$ and $c'$ be natural numbers with $1 \le \ell$, and let $a,d$ be integers satisfying $a d \equiv 1 \pmod{\ell c'}$ (the congruence being taken in $\mathbb{Z}$ with modulus the integer cast of the natural number $\ell c'$). Here, for an integer $h$ and a natural number $k$, the Dedekind sum is $\mathrm{dedekindSum}(h,k) = \sum_{r=0}^{k-1} \big((r/k)\big)\,\big((hr/k)\big)$, where the sawtooth $((x))$ is defined to be $0$ when the fractional part of $x$ vanishes and $\operatorname{frac}(x) - 1/2$ otherwise (so the sum is empty, hence $0$, when $k = 0$). The assertion is that there exists an integer $z$ with
--   $$12\left(\frac{(a+d)(1-\ell)}{12\,\ell c'} + \mathrm{dedekindSum}(d,c') - \mathrm{dedekindSum}(d,\ell c')\right) = \gcd(\ell-1,12)\, z,$$
--   all terms being computed in $\mathbb{Q}$; the quotient uses the convention $x/0 = 0$, and $\ell - 1$ is truncated subtraction of natural numbers, so $\gcd(\ell - 1, 12)$ is the greatest common divisor of the natural numbers $\ell - 1$ and $12$, equal to $12$ when $\ell = 1$.
--
--   This is Rademacher's congruence for the function $\Phi$ attached to $\eta$: the bracketed quantity is $\tfrac{1}{12}\big(\Phi(\gamma) - \Phi(\gamma')\big)$ for $\gamma = \begin{pmatrix} a & b \\ \ell c' & d\end{pmatrix} \in \Gamma_0(\ell)$ and its conjugate $\gamma' = \begin{pmatrix} a & \ell b \\ c' & d\end{pmatrix}$, and divisibility by $\gcd(\ell-1,12)$ is what makes the eta quotient $(\eta(\tau)/\eta(\ell\tau))^{24/\gcd(\ell-1,12)}$ invariant under $\Gamma_0(\ell)$. It is used by [`ModularCurve.sharpUnitInvariant`](thm.html#ModularCurve.sharpUnitInvariant) and by [`ModularCurve.sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_rademacher_phi_level_congruence.lean

import Definitions.Def_NumberTheory_DedekindSum
import Mathlib.Data.Int.ModEq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem rademacher_phi_level_congruence (ℓ c' : ℕ) (hℓ : 1 ≤ ℓ) (a d : ℤ) (h1 : Int.ModEq ((ℓ * c' : ℕ) : ℤ) (a * d) 1) : ∃ z : ℤ, 12 * (((a + d : ℤ) : ℚ) * (1 - (ℓ : ℚ)) / (12 * ((ℓ * c' : ℕ) : ℚ)) + dedekindSum d c' - dedekindSum d (ℓ * c')) = ((Nat.gcd (ℓ - 1) 12 : ℕ) : ℚ) * z := by sorry
