-- Prove2me | Theorems.Thm_rademacher_phi_level_witness_five
-- name    : rademacher_phi_level_witness_five
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/1427c4a7-f789-521b-b310-6db08549fb39
-- title:
--   Rademacher Φ witness for ℓ≡ 5(mod 12)
-- statement:
--   For every natural number $j$ — the statement carries no hypotheses — put $\ell = 12j+5$ and $a = 4j+2$, and let $s(h,k)=\sum_{r=0}^{k-1}\langle r/k\rangle\,\langle hr/k\rangle$ be the Dedekind sum built from the sawtooth $\langle x\rangle$ that is $0$ when the fractional part of $x$ vanishes and $\operatorname{frac}(x)-\tfrac12$ otherwise ([`dedekindSum`](def/NumberTheory_DedekindSum.html#L73), [`dedekindSaw`](def/NumberTheory_DedekindSum.html#L11)). The assertion is a conjunction of two parts. First, the identity in $\mathbb{Q}$
--   $$12\left(\frac{(a+3)\,(1-\ell)}{12\,\ell} + s(3,1) - s(3,\ell)\right) = \gcd(\ell-1,12)\cdot\bigl(-(2j+1)\bigr),$$
--   where $a+3$ is formed in $\mathbb{Z}$ and $\ell-1$, the greatest common divisor and the casts are taken in $\mathbb{N}$ (so $\ell - 1 = 12j+4$ and $\gcd(12j+4,12)=4$, making the right-hand side $-(8j+4)$). Secondly, the natural number $|{-(2j+1)}| = 2j+1$ is coprime to $(\ell-1)/\gcd(\ell-1,12) = 3j+1$, the quotient being natural division.
--
--   This is the explicit evaluation, for the level class $\ell \equiv 5 \pmod{12}$, of the combination of Dedekind sums occurring in the Rademacher $\Phi$-function attached to the matrix with entries $a = 4j+2$ and $d = 3$ (so that $ad \equiv 1 \pmod \ell$), together with the coprimality needed for the value to generate the relevant cyclic group. It is consumed by [`ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_five`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_five), which supplies a necessary condition for levels congruent to $5$ modulo $12$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_rademacher_phi_level_witness_five.lean

import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem rademacher_phi_level_witness_five (j : ℕ) : 12 * ((((4 * j + 2 : ℕ) + 3 : ℤ) : ℚ) * (1 - ((12 * j + 5 : ℕ) : ℚ)) / (12 * ((12 * j + 5 : ℕ) : ℚ)) + dedekindSum 3 1 - dedekindSum 3 (12 * j + 5)) = ((Nat.gcd ((12 * j + 5) - 1) 12 : ℕ) : ℚ) * (-(2 * (j : ℤ) + 1)) ∧ Nat.Coprime (Int.natAbs (-(2 * (j : ℤ) + 1))) (((12 * j + 5) - 1) / Nat.gcd ((12 * j + 5) - 1) 12) := by sorry
