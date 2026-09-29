-- Prove2me | Theorems.Thm_flt_regular
-- name    : flt_regular
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/67ddbf06-eeeb-54b8-b928-606458315141
-- title:
--   Kummer's theorem: Fermat's Last Theorem for regular primes
-- statement:
--   Let $p$ be a natural number carrying an instance of `Fact p.Prime`, so that $p$ is prime. Two hypotheses are imposed. First, `hreg`: $p$ is coprime, in the sense of `Nat.Coprime`, to `Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ)))`, the order of the ideal class group of the ring of integers of the $p$-th cyclotomic field $\mathbb{Q}(\zeta_p)$ — that is, $\gcd(p, h(\mathbb{Q}(\zeta_p))) = 1$, which for prime $p$ amounts to $p \nmid h(\mathbb{Q}(\zeta_p))$, the regularity of $p$. Here `CyclotomicField p ℚ` is Mathlib's $p$-th cyclotomic extension of $\mathbb{Q}$ and the finiteness of the class group is supplied by the ambient number-field instances. Second, `hodd`: $p \neq 2$, so $p$ is an odd prime. The conclusion is `FermatLastTheoremFor p`, Mathlib's predicate asserting that for all natural numbers $a, b, c$ with $a \neq 0$, $b \neq 0$ and $c \neq 0$ one has $a^p + b^p \neq c^p$; equivalently (and this is the form used in the proof) there is no triple of nonzero integers $a, b, c$ with $a^p + b^p = c^p$. Thus: for every odd prime $p$ not dividing the class number of $\mathbb{Q}(\zeta_p)$, the Fermat equation of exponent $p$ has no solution in nonzero integers. No assumption of coprimality of $a, b, c$, and no restriction on the divisibility of $abc$ by $p$, is made.
--
--   This is Kummer's theorem on Fermat's Last Theorem for regular primes, in the usual formulation except that regularity is expressed as coprimality of $p$ with the full class number $h(\mathbb{Q}(\zeta_p))$ rather than with the relative class number $h^-$, and the excluded exponent $p = 2$ is stated as the hypothesis $p \neq 2$. Within the present development it serves to settle the exponents $7$, $11$ and $13$ outright: [`fermatLastTheoremSeven`](thm.html#fermatLastTheoremSeven), [`fermatLastTheoremEleven`](thm.html#fermatLastTheoremEleven) and [`fermatLastTheoremThirteen`](thm.html#fermatLastTheoremThirteen) each combine it with a proof that the ring of integers of the corresponding cyclotomic field is principal, so that the class number is $1$ and the coprimality hypothesis is automatic. Those three exponents, together with $5$, are exactly the ones at which the Eisenstein-ideal argument for irreducibility of the mod $p$ representation of a Frey curve is unavailable, and for which the relevant statement is instead made vacuous.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_flt_regular.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open scoped NumberField

theorem flt_regular {p : ℕ} [Fact p.Prime] (hreg : p.Coprime (Fintype.card (ClassGroup (𝓞 (CyclotomicField p ℚ))))) (hodd : p ≠ 2) : FermatLastTheoremFor p := by sorry
