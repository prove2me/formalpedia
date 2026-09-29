-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_channelEvent_eq_zero_of_not_dvd
-- name    : ErdosProblems.Erdos68.channelEvent_eq_zero_of_not_dvd
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:11:54.361434+00:00
-- url     : https://prove2.me/theorems/fffa4585-9b87-43f0-9554-668feb1dfa2d
-- title:
--   Channel Event eq zero of not divisibility
-- statement:
--   If d≥2 does not divide n, the channel event at n is zero.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/FactorialChannelCertificate.lean#L68-L100
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

theorem ErdosProblems.Erdos68.channelEvent_eq_zero_of_not_dvd
    {d n : ℕ} (hd : 2 ≤ d) (hnd : ¬ d ∣ n) :
    channelEvent d n = 0 := by sorry
