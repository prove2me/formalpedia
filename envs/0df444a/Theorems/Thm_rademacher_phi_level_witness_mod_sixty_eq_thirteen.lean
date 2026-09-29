-- Prove2me | Theorems.Thm_rademacher_phi_level_witness_mod_sixty_eq_thirteen
-- name    : rademacher_phi_level_witness_mod_sixty_eq_thirteen
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/654430e5-fb9a-54e6-a15c-1370de0bd300
-- title:
--   Rademacher Φ witness for ℓ≡ 13(mod 60)
-- statement:
--   Let $i$ be a natural number, and set $\ell=60i+13$ and $a=36i+8$. Here $\operatorname{dedekindSum} h\,k=\sum_{r=0}^{k-1}((r/k))\,((hr/k))$ for $h\in\mathbb{Z}$ and $k\in\mathbb{N}$, where $((x))$ is the sawtooth function [`dedekindSaw`](def/NumberTheory_DedekindSum.html#L11), equal to $0$ when the fractional part of $x$ vanishes and to $\{x\}-1/2$ otherwise. The assertion is the conjunction of two statements. First, the rational identity
--   $$12\Big(\frac{(a+5)(1-\ell)}{12\,\ell}+s(5,1)-s(5,\ell)\Big)=\gcd(\ell-1,12)\cdot\big(-(4i+1)\big),$$
--   where $s(5,1)$ and $s(5,\ell)$ are the above Dedekind sums with $h=5$ and $k=1$, $k=\ell$ respectively, the numerator $a+5$ is formed in $\mathbb{Z}$ and then mapped to $\mathbb{Q}$, and $\ell-1=60i+12$ is the truncated natural subtraction. Second, the natural numbers $|-(4i+1)|=4i+1$ and $(\ell-1)/\gcd(\ell-1,12)$ are coprime; since $\gcd(60i+12,12)=12$, the latter is $5i+1$, so the right-hand side above equals $-12(4i+1)$ and the coprimality says $\gcd(4i+1,5i+1)=1$. No hypothesis is imposed on $i$; in particular $\ell$ need not be prime.
--
--   The bracketed expression is the value of the Rademacher $\Phi$-invariant attached to the matrix with lower row $(\ell,5)$ and upper entry $a=36i+8$ (so that $a\cdot 5\equiv 1 \pmod{\ell}$), normalised by $12$ and expressed through Dedekind sums. It serves as the explicit witness for the congruence class $\ell\equiv 13 \pmod{60}$ feeding [`ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirteen`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirteen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_rademacher_phi_level_witness_mod_sixty_eq_thirteen.lean

import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem rademacher_phi_level_witness_mod_sixty_eq_thirteen (i : ℕ) : 12 * ((((36 * i + 8 : ℕ) + 5 : ℤ) : ℚ) * (1 - ((60 * i + 13 : ℕ) : ℚ)) / (12 * ((60 * i + 13 : ℕ) : ℚ)) + dedekindSum 5 1 - dedekindSum 5 (60 * i + 13)) = ((Nat.gcd ((60 * i + 13) - 1) 12 : ℕ) : ℚ) * (-(4 * (i : ℤ) + 1)) ∧ Nat.Coprime (Int.natAbs (-(4 * (i : ℤ) + 1))) (((60 * i + 13) - 1) / Nat.gcd ((60 * i + 13) - 1) 12) := by sorry
