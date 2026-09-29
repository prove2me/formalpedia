-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_channelEvent_eq_of_dvd
-- name    : ErdosProblems.Erdos68.channelEvent_eq_of_dvd
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:06:35.036468+00:00
-- url     : https://prove2.me/theorems/c5a24fd5-fcb4-4d43-873c-265e6fbdd994
-- title:
--   Channel Event eq of divisibility
-- statement:
--   If d≥2 divides positive n, the channel event at n equals (d!−1) times the channel weight at n.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/DivisorChannelBasis.lean#L155-L199
--   Correspondence: finite channel-moment analysis for Erdős #68. No novelty or whole-problem claim.

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

/-!
# Divisor-coordinate channel basis for Erdős problem 68

The adjacent difference `T_n = n e_{n-1} - e_n` hits exactly the divisor
channels of index `n`.  Subtracting proper-divisor copies produces an
integral family `U_n` with a single nonzero channel.  On the manuscript
support `n ≥ 2`, the second channel forces an extra factor of `12` in the
moment, so annihilating channels through `D` yields `12 L_D ∣ M`.

No declaration here constructs a cofinal nonintegrality family or decides
rationality of the factorial-gap series.
-/


open Finsupp

/-! ## Linearity of the Finsupp channel presentation -/





























/-! ## Adjacent differences `T_n` -/

open ErdosProblems.Erdos68

theorem ErdosProblems.Erdos68.channelEvent_eq_of_dvd
    {d n : ℕ} (hd : 2 ≤ d) (hn : 0 < n) (hnd : d ∣ n) :
    channelEvent d n =
      ((d.factorial : ℤ) - 1) * (channelWeight n d : ℤ) := by sorry
