-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_channelWeight_mul_denominator
-- name    : ErdosProblems.Erdos68.channelWeight_mul_denominator
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:05:39.677332+00:00
-- url     : https://prove2.me/theorems/5d78e740-c499-4418-89e2-e839b09b6cc2
-- title:
--   Channel Weight mul denominator
-- statement:
--   For positive d, multiplying the integral channel weight at i by (d factorial) to the power floor(i/d) gives i factorial.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L46-L51
--   Correspondence: finite channel-moment analysis for Erdős #68. No novelty or whole-problem claim.

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
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

open ErdosProblems.Erdos68

theorem ErdosProblems.Erdos68.channelWeight_mul_denominator
    (i d : ℕ) (hd : 0 < d) :
    d.factorial ^ (i / d) * channelWeight i d =
      i.factorial := by sorry
