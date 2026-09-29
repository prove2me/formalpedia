-- Prove2me | solution 1 for ErdosProblems.Erdos68.channelNumerator_sum
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:16:39.405869+00:00
-- url     : https://prove2.me/submissions/9d0c0a6e-1867-49a1-83fa-e7b012687e21

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_add
import Theorems.Thm_ErdosProblems_Erdos68_channelNumerator_zero
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

namespace ErdosProblems.Erdos68
open Finsupp

/-! ## Linearity of the Finsupp channel presentation -/
end ErdosProblems.Erdos68

open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
theorem solution {ι : Type*} (s : Finset ι) (f : ι → ℕ →₀ ℤ)
    (d : ℕ) :
    channelNumerator (∑ i ∈ s, f i) d =
      ∑ i ∈ s, channelNumerator (f i) d := by
  classical
  induction s using Finset.induction with
  | empty => simp [channelNumerator_zero]
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi, channelNumerator_add, ih]
