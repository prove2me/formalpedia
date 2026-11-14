-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
-- name    : GreenTaoPort_Wikipedia_GreenTao_Sieve_TruncatedDivisorSum
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:48:21.734399+00:00
-- url     : https://prove2.me/theorems/e8212144-c43f-4916-9079-8dca8a251a7b
-- title:
--   Smooth Möbius divisor sums and normalized Selberg weights
-- statement:
--   For a real function $\chi$ and natural numbers $R,n$, define the smoothly truncated divisor sum
--
--   $$
--   \Lambda_{\chi,R}(n)=\log R\sum_{d\mid n}\mu(d)\chi\!\left(\frac{\log d}{\log R}\right).
--   $$
--
--   The summation is over natural divisors, and the individual summand is also supplied separately. The Selberg weight is the square $\Lambda_{\chi,R}(n)^2$. Given a real normalizer $c_\chi$ and natural period $W$, its normalized majorant is
--
--   $$
--   \frac{\varphi(W)}{W}\,\frac{\Lambda_{\chi,R}(n)^2}{c_\chi\log R}.
--   $$
--
--   These are total real-valued definitions. Smoothness, compact support, $\chi(0)=1$, and positivity assumptions are supplied when proving the later majorant estimates rather than imposed on the function parameter here.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Sieve/TruncatedDivisorSum.lean#L21-L206

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic
import Lean

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


/-!
# Smooth truncated divisor sums

The Goldston--Yıldırım majorant is the square of a smoothly truncated
Möbius divisor sum.  This file fixes the normalization and proves the exact
prime-value identity used for pointwise domination of the W-tricked prime
weight.  The later linear-forms estimate is deliberately separated from
these elementary identities.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped ArithmeticFunction.Moebius BigOperators

/-- Smooth truncated divisor sum

`Λ_{χ,R}(n) = log R * ∑_{d ∣ n} μ(d) χ(log d / log R)`.

For the final construction, `χ` is a smooth compactly supported function
with `χ 0 = 1`. -/
noncomputable def smoothTruncatedDivisorSum
    (χ : ℝ → ℝ) (R n : ℕ) : ℝ :=
  Real.log R *
    ∑ d ∈ n.divisors,
      (ArithmeticFunction.moebius d : ℝ) *
        χ (Real.log d / Real.log R)

/-- The individual Möbius-cutoff term in the truncated divisor sum. -/
noncomputable def smoothDivisorSummand
    (χ : ℝ → ℝ) (R d : ℕ) : ℝ :=
  (ArithmeticFunction.moebius d : ℝ) *
    χ (Real.log d / Real.log R)















/-- The nonnegative Selberg square used as the unnormalized majorant. -/
noncomputable def smoothSelbergWeight
    (χ : ℝ → ℝ) (R n : ℕ) : ℝ :=
  smoothTruncatedDivisorSum χ R n ^ 2











/-- The standard W-tricked normalization of the Selberg square.  The
positive constant `cχ` will later be the `L²` mass of `χ'`. -/
noncomputable def normalizedSelbergMajorant
    (χ : ℝ → ℝ) (cχ : ℝ) (R W n : ℕ) : ℝ :=
  (W.totient : ℝ) / W *
    smoothSelbergWeight χ R n / (cχ * Real.log R)





end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.smoothDivisorSummand.eq_1,
    `Wikipedia.SzemeredisTheorem.smoothSelbergWeight.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


