-- Prove2me | Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
-- name    : ErdosProblems_Erdos68_FactorialChannelCertificate
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T15:42:51.041766+00:00
-- url     : https://prove2.me/theorems/2e6d091c-6b6e-453f-825e-4308fcb6cebe
-- title:
--   Factorial-channel weights and finite-vector observables
-- statement:
--   Defines the integral channel weight, the channel numerator and factorial moment of a finite signed coefficient vector, and the consecutive-weight channel event. Their arithmetic properties are separate theorem nodes.
-- source:
--   Pinned Lean definition channelWeight: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L42-L43
--   Pinned Lean definition channelNumerator: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L54-L55
--   Pinned Lean definition factorialMoment: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L58-L59
--   Pinned Lean definition channelEvent: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L62-L64
--   Correspondence: finite channel-moment analysis for Erdős #68. No novelty or whole-problem claim.

import Lean.Elab.Tactic.Omega
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

/-!
# Erdős #68: factorial-channel certificates

For each divisor channel `d`, the weight

`i! / (d!)^(⌊i/d⌋)`

is integral, and consecutive weights obey the factorial recurrence except at
indices divisible by `d`.  The coefficient vector `λ = 2e₃ - e₄` then gives
an explicit finite certificate: its channel values and factorial moment can be
computed exactly, and the stated elementary enclosure for the remaining tail
places its residual strictly between `-1` and `0`.

This is a single finite certificate.  It does not supply a cofinal family of
nonzero residuals or prove irrationality of the Erdős #68 series.
-/

namespace ErdosProblems.Erdos68



/-- Integral weight of index `i` in the divisor channel `d`. -/
def channelWeight (i d : ℕ) : ℕ :=
  i.factorial / (d.factorial ^ (i / d))



/-- Finite-support integer numerator in channel `d`. -/
def channelNumerator (lam : ℕ →₀ ℤ) (d : ℕ) : ℤ :=
  lam.sum fun i z => z * (channelWeight i d : ℤ)

/-- The factorial moment of a finite-support coefficient vector. -/
def factorialMoment (lam : ℕ →₀ ℤ) : ℤ :=
  lam.sum fun i z => z * (i.factorial : ℤ)

/-- Sparse recurrence event between consecutive channel columns. -/
def channelEvent (d n : ℕ) : ℤ :=
  n * (channelWeight (n - 1) d : ℤ) -
    (channelWeight n d : ℤ)























end ErdosProblems.Erdos68


