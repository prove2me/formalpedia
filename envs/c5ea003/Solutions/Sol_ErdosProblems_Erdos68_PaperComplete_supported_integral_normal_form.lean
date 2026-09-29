-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.supported_integral_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-28T00:57:00.747284+00:00
-- url     : https://prove2.me/submissions/66ed1a1e-69ab-41a8-a329-36de37cf4b79

import Definitions.Def_ErdosProblems_Erdos68_ChannelBreakpointRigidity
import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Theorems.Thm_ErdosProblems_Erdos68_channelModulus_dvd_moment_sub_channel
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

namespace ErdosProblems.Erdos68.PaperComplete
end ErdosProblems.Erdos68.PaperComplete

/-!
# Literal support-sensitive normal-form and band statements

The assumptions below concern only nonzero coefficients in lambda.support.
They do not require an arbitrary list's zero-coefficient entries to satisfy
support restrictions. These are the Finsupp forms of long res:normalform and
res:bandbreakpoint. All pointwise arithmetic is reused from the supplied source.
-/

namespace ErdosProblems.Erdos68.PaperComplete
open scoped BigOperators
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution (f : ℕ →₀ ℤ) {d : ℕ} (hd : 2 ≤ d) :
    ∃ k : ℤ, channelNumerator f d = factorialMoment f + ((d.factorial : ℤ) - 1) * k := by
  obtain ⟨k, hk⟩ := channelModulus_dvd_moment_sub_channel f hd
  refine ⟨-k, ?_⟩
  linarith
