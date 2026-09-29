-- Prove2me | Theorems.Thm_rademacher_phi_level_witness_mod_oneTwenty_eq_oneHundredNine
-- name    : rademacher_phi_level_witness_mod_oneTwenty_eq_oneHundredNine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/538a2090-5c68-5706-963f-eb4fae56cfd7
-- title:
--   Dedekind-sum phase identity at levels ≡ 109 (mod 120)
-- statement:
--   Here $\mathrm{dedekindSum}\,h\,k$ denotes, for an integer $h$ and a natural number $k$, the finite sum $\sum_{r=0}^{k-1}\big(\!\!\big(r/k\big)\!\!\big)\,\big(\!\!\big(hr/k\big)\!\!\big)$, where the sawtooth $\big(\!\!\big(x\big)\!\!\big)$ is defined as $0$ when the fractional part of $x$ vanishes and as $\{x\}-1/2$ otherwise. For every natural number $j$, write $\ell = 120j+109$ and $a = 24j+22$. The assertion is a conjunction of two statements. First, the identity of rational numbers $$12\left(\frac{(a+5)(1-\ell)}{12\,\ell} + \mathrm{dedekindSum}\,5\,1 - \mathrm{dedekindSum}\,5\,\ell\right) = \gcd(\ell-1,12)\cdot\big(-(4j+4)\big),$$ where $\gcd$ is the greatest common divisor of natural numbers, $\ell-1$ being formed by truncated subtraction, and both the gcd and the integer $-(4j+4)$ are cast into $\mathbb{Q}$. Second, the natural numbers $|-(4j+4)|$ and $(\ell-1)/\gcd(\ell-1,12)$, the latter a truncated natural division, are coprime. Since $\gcd(120j+108,12)=12$, the right-hand side of the identity is $-48(j+1)$ and the second factor in the coprimality assertion is $10j+9$.
--
--   The left-hand side is the Rademacher phase attached to the residue $5$ at level $\ell$, and the quantity $(\ell-1)/\gcd(\ell-1,12)$ is the Eisenstein numerator of that level; the statement thus exhibits, for every level congruent to $109$ modulo $120$, a phase value coprime to the Eisenstein numerator. It is used by [`ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_one`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_one) in the necessity half of a sharp-unit criterion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_rademacher_phi_level_witness_mod_oneTwenty_eq_oneHundredNine.lean

import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem rademacher_phi_level_witness_mod_oneTwenty_eq_oneHundredNine (j : ℕ) : 12 * ((((24 * j + 22 : ℕ) + 5 : ℤ) : ℚ) * (1 - ((120 * j + 109 : ℕ) : ℚ)) / (12 * ((120 * j + 109 : ℕ) : ℚ)) + dedekindSum 5 1 - dedekindSum 5 (120 * j + 109)) = ((Nat.gcd ((120 * j + 109) - 1) 12 : ℕ) : ℚ) * (-(4 * (j : ℤ) + 4)) ∧ Nat.Coprime (Int.natAbs (-(4 * (j : ℤ) + 4))) (((120 * j + 109) - 1) / Nat.gcd ((120 * j + 109) - 1) 12) := by sorry
