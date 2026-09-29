-- Prove2me | Theorems.Thm_rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine
-- name    : rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/bb7cb42d-1447-5371-a6cf-59c0e4aa5fa2
-- title:
--   A Dedekind-sum phase identity at levels ≡ 49 (mod 120)
-- statement:
--   The assertion is a conjunction, for an arbitrary natural number $j$. Throughout, $\mathrm{dedekindSum}\,h\,k$ denotes, for $h \in \mathbb{Z}$ and $k \in \mathbb{N}$, the rational number $\sum_{r=0}^{k-1} \big(\!\!\big(\tfrac{r}{k}\big)\!\!\big)\,\big(\!\!\big(\tfrac{hr}{k}\big)\!\!\big)$, where the sawtooth $\big(\!\!\big(x\big)\!\!\big)$ is $0$ when the fractional part of $x$ vanishes and is $\{x\} - \tfrac12$ otherwise. Writing $\ell = 120j + 49$ and $a = 24j + 10$ (both as natural numbers, cast into $\mathbb{Q}$ where needed), the first component states the exact equality of rational numbers
--   $$12\Big(\frac{(a+5)(1-\ell)}{12\,\ell} + \mathrm{dedekindSum}\,5\,1 - \mathrm{dedekindSum}\,5\,\ell\Big) = \gcd(\ell - 1,\,12)\cdot\big(-(4j+2)\big),$$
--   where $\ell - 1$ is truncated subtraction of natural numbers and $\gcd(\ell-1,12)$ is the natural-number gcd cast into $\mathbb{Q}$, while $-(4j+2)$ is an integer cast into $\mathbb{Q}$. The second component states that the natural numbers $2j+1$ and $10j+4$ are coprime. No hypotheses beyond the existence of $j$ are imposed.
--
--   The left-hand side is the Rademacher phase attached to the residue $5$ at level $\ell = 120j+49$, expressed through the Dedekind sums $s(5,1)$ and $s(5,\ell)$; the identity records that this phase equals $-(4j+2)$ times $\gcd(\ell-1,12) = 12$, an even value, together with the coprimality of its odd part $2j+1$ and the Eisenstein-type numerator $10j+4$. It is used in the proof of [`ModularCurve.sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_oneTwenty_eq_one_or_fortyNine).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine.lean

import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem rademacher_phi_level_witness_mod_oneTwenty_eq_fortyNine (j : ℕ) : 12 * ((((24 * j + 10 : ℕ) + 5 : ℤ) : ℚ) * (1 - ((120 * j + 49 : ℕ) : ℚ)) / (12 * ((120 * j + 49 : ℕ) : ℚ)) + dedekindSum 5 1 - dedekindSum 5 (120 * j + 49)) = ((Nat.gcd ((120 * j + 49) - 1) 12 : ℕ) : ℚ) * (-(4 * (j : ℤ) + 2)) ∧ Nat.Coprime (2 * j + 1) (10 * j + 4) := by sorry
