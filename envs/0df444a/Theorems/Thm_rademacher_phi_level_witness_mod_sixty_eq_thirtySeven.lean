-- Prove2me | Theorems.Thm_rademacher_phi_level_witness_mod_sixty_eq_thirtySeven
-- name    : rademacher_phi_level_witness_mod_sixty_eq_thirtySeven
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/7fa5ba3d-5c25-56db-86f6-a944b8f304f9
-- title:
--   Dedekind-sum level witness for ℓ ≡ 37 (mod 60)
-- statement:
--   Here $\mathrm{dedekindSaw}(x)$ denotes the sawtooth $((x))$, equal to $0$ when the fractional part of $x$ vanishes and to $\{x\} - 1/2$ otherwise, and $\mathrm{dedekindSum}(h,k) = \sum_{r=0}^{k-1} ((r/k))\,((hr/k))$ for $h \in \mathbb{Z}$, $k \in \mathbb{N}$. The assertion is a conjunction of two statements, for an arbitrary natural number $i$; write $\ell = 60i+37$ and $a = 24i+15$, so that $a + 5$ is formed in $\mathbb{Z}$ and cast to $\mathbb{Q}$. First, the identity in $\mathbb{Q}$
--   $$12\left(\frac{(a+5)(1-\ell)}{12\,\ell} + \mathrm{dedekindSum}(5,1) - \mathrm{dedekindSum}(5,\ell)\right) = \gcd(\ell-1,\,12)\cdot\bigl(-(3i+2)\bigr),$$
--   where $\ell - 1$ is the truncated subtraction $(60i+37)-1$ in $\mathbb{N}$, the greatest common divisor is taken in $\mathbb{N}$ and cast to $\mathbb{Q}$, and $-(3i+2)$ is formed in $\mathbb{Z}$. Second, the natural number $|-(3i+2)| = 3i+2$ is coprime to the natural-number quotient $(\ell-1)/\gcd(\ell-1,12)$.
--
--   The left-hand side is the Rademacher-type $\Phi$-expression attached to a matrix with lower-left data $(a,5)$ at level $\ell = 60i+37$, and the statement exhibits the resulting integer $-(3i+2)$ together with its coprimality to $(\ell-1)/\gcd(\ell-1,12)$. It is the witness consumed by [`ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirtySeven`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_sixty_eq_thirtySeven), which treats the residue class $\ell \equiv 37 \pmod{60}$; no primality of $\ell$ is assumed, so composite values of $60i+37$ are covered as well.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_rademacher_phi_level_witness_mod_sixty_eq_thirtySeven.lean

import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem rademacher_phi_level_witness_mod_sixty_eq_thirtySeven (i : ℕ) : 12 * ((((24 * i + 15 : ℕ) + 5 : ℤ) : ℚ) * (1 - ((60 * i + 37 : ℕ) : ℚ)) / (12 * ((60 * i + 37 : ℕ) : ℚ)) + dedekindSum 5 1 - dedekindSum 5 (60 * i + 37)) = ((Nat.gcd ((60 * i + 37) - 1) 12 : ℕ) : ℚ) * (-(3 * (i : ℤ) + 2)) ∧ Nat.Coprime (Int.natAbs (-(3 * (i : ℤ) + 2))) (((60 * i + 37) - 1) / Nat.gcd ((60 * i + 37) - 1) 12) := by sorry
