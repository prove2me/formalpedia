-- Prove2me | Theorems.Thm_rademacher_phi_level_witness_eleven
-- name    : rademacher_phi_level_witness_eleven
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/4da687e3-efc6-5721-acfe-d326f5e58532
-- title:
--   Dedekind-sum witness for levels ℓ ≡ 11 (mod 12)
-- statement:
--   Here $s(h,k)=\sum_{r=0}^{k-1}\big(\!\big(\tfrac rk\big)\!\big)\big(\!\big(\tfrac{hr}{k}\big)\!\big)$ is [`dedekindSum`](def/NumberTheory_DedekindSum.html#L73), built from the sawtooth [`dedekindSaw`](def/NumberTheory_DedekindSum.html#L11) which sends $x$ to $0$ when its fractional part vanishes and to $\{x\}-\tfrac12$ otherwise. The assertion is, for every natural number $j$, a conjunction of two statements about $\ell=12j+11$ and $a=4j+4$. First, the identity in $\mathbb{Q}$
--   $$12\left(\frac{(a+3)(1-\ell)}{12\,\ell}+s(3,1)-s(3,\ell)\right)=\gcd(\ell-1,12)\cdot\big(-(4j+4)\big),$$
--   where $a+3$ is formed in $\mathbb{Z}$ and then cast, and $\ell-1$ is the truncated subtraction $(12j+11)-1$ in $\mathbb{N}$. Secondly, the natural numbers $|-(4j+4)|=4j+4$ and $(\ell-1)/\gcd(\ell-1,12)$ are coprime, the quotient being taken in $\mathbb{N}$. There are no hypotheses beyond $j\in\mathbb{N}$; in particular $\ell$ is not assumed prime, so the statement covers composite $\ell\equiv 11 \pmod{12}$ as well.
--
--   This is the explicit evaluation of the Rademacher $\Phi$-type expression attached to the matrix data $a=4j+4$, $d=3$ at level $\ell=12j+11$, together with the coprimality of the resulting integer to $(\ell-1)/\gcd(\ell-1,12)$. It is the witness consumed by [`ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_eleven`](thm.html#ModularCurve.sharpUnitNecessary_of_mod_twelve_eq_eleven), which handles the level class $\ell\equiv 11 \pmod{12}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_rademacher_phi_level_witness_eleven.lean

import Definitions.Def_NumberTheory_DedekindSum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem rademacher_phi_level_witness_eleven (j : ℕ) : 12 * ((((4 * j + 4 : ℕ) + 3 : ℤ) : ℚ) * (1 - ((12 * j + 11 : ℕ) : ℚ)) / (12 * ((12 * j + 11 : ℕ) : ℚ)) + dedekindSum 3 1 - dedekindSum 3 (12 * j + 11)) = ((Nat.gcd ((12 * j + 11) - 1) 12 : ℕ) : ℚ) * (-(4 * (j : ℤ) + 4)) ∧ Nat.Coprime (Int.natAbs (-(4 * (j : ℤ) + 4))) (((12 * j + 11) - 1) / Nat.gcd ((12 * j + 11) - 1) 12) := by sorry
