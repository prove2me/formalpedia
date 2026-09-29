-- Prove2me | Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
-- name    : ErdosProblems_Erdos68_PaperCompleteMomentHorizon
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T15:49:27.875958+00:00
-- url     : https://prove2.me/theorems/05eb6be4-d61f-4180-8f18-b03d46c6f7ae
-- title:
--   Scalar tail gcd definitions
-- statement:
--   Defines the isolated unit’s first-coordinate scalar, a finite scalar gcd, and the universal-property predicate for the full tail gcd. The quadratic-horizon theorem is a separate theorem node.
-- source:
--   Pinned Lean definition channelScalar: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteMomentHorizon.lean#L25-L25
--   Pinned Lean definition finiteScalarGcd: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteMomentHorizon.lean#L157-L158
--   Pinned Lean definition IsScalarTailGcd: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteMomentHorizon.lean#L161-L162
--   Correspondence: finite channel-moment analysis for Erdős #68. No novelty or whole-problem claim.

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Combinatorics.Enumerative.Bell
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.GCD.Prime
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Rat.Lemmas
import Mathlib.NumberTheory.Divisors
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.NatFactorial
import Mathlib.Tactic.Ring

/-!
# The actual factorial specialisation of the quadratic tail-gcd theorem

Short-note label: res:finite-channel-moment-certificate.

This file does not assume a recurrence for an arbitrary sequence or assume
unordered-block divisibility. It derives the recurrence for U_n(1) from the
supplied definition and obtains the block identity from Mathlib's
Nat.uniformBell_mul_eq. The gcd of an infinite family is represented by its
universal property (all common divisors), avoiding an arbitrary choice of a
generator in Z. This is the exact gcd assertion, not a weaker bound.

STATUS: compiled proof candidate. No new axioms, no proof placeholders.
-/
namespace ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators

noncomputable def channelScalar (n : ℕ) : ℤ := isolatedChannelUnit n 1



















noncomputable def finiteScalarGcd (D N : ℕ) : ℕ :=
  (Finset.Icc (D + 1) N).gcd (fun n => (channelScalar n).natAbs)

/-- The universal property that uniquely specifies the positive tail gcd. -/
def IsScalarTailGcd (D G : ℕ) : Prop :=
  ∀ b : ℕ, b ∣ G ↔ ∀ n : ℕ, D < n → (b : ℤ) ∣ channelScalar n











end ErdosProblems.Erdos68.PaperComplete


