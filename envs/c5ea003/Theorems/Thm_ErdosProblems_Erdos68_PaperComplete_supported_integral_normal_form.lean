-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_supported_integral_normal_form
-- name    : ErdosProblems.Erdos68.PaperComplete.supported_integral_normal_form
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-28T00:56:18.198861+00:00
-- url     : https://prove2.me/theorems/d5b5c593-49ef-4cbc-bbe8-0d79a851c5e0
-- title:
--   Integral normal form on finite support
-- statement:
--   For every finitely supported integer coefficient vector f and every natural d at least 2, there is an integer k such that the channel numerator at d equals the factorial moment plus (d! − 1)k.
-- source:
--   Pinned Lean theorem: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteSupportedBands.lean#L16-L21; this is the literal finite-support Finsupp normal form associated with the source paper result, without an irrationality or independent-review claim.

import Definitions.Def_ErdosProblems_Erdos68_ChannelBreakpointRigidity
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

open scoped BigOperators

open ErdosProblems.Erdos68.PaperComplete

theorem ErdosProblems.Erdos68.PaperComplete.supported_integral_normal_form (f : ℕ →₀ ℤ) {d : ℕ} (hd : 2 ≤ d) :
    ∃ k : ℤ, channelNumerator f d = factorialMoment f + ((d.factorial : ℤ) - 1) * k := by sorry
