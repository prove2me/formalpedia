-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_sub
-- name    : ErdosProblems.Erdos68.channelNumerator_sub
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:12:03.748989+00:00
-- url     : https://prove2.me/theorems/01b92a8c-e66b-4d0d-8d87-984b9443fec3
-- title:
--   Channel Numerator sub
-- statement:
--   The channel numerator of a difference is the difference of the two numerators.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/DivisorChannelBasis.lean#L53-L56
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

open ErdosProblems.Erdos68

theorem ErdosProblems.Erdos68.channelNumerator_sub (f g : ℕ →₀ ℤ) (d : ℕ) :
    channelNumerator (f - g) d =
      channelNumerator f d - channelNumerator g d := by sorry
