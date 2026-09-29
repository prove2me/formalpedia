-- Prove2me | solution 1 for ErdosProblems.Erdos68.PaperComplete.finite_channel_moment_certificate
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:29:35.051053+00:00
-- url     : https://prove2.me/submissions/b892da42-634d-4923-b314-f15c233efaf7

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
import Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_quadratic_scalar_tail_gcd
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
end ErdosProblems.Erdos68.PaperComplete

open scoped BigOperators
open ErdosProblems in
open ErdosProblems.Erdos68 in
open ErdosProblems.Erdos68.PaperComplete in
theorem solution {D p : ℕ}
    (hD : 2 ≤ D) (hp : p.Prime) (hDp : D / 2 < p) (hpD : p ≤ D) :
    let H := D * (2 * p - 1)
    0 < finiteScalarGcd D H ∧
      IsScalarTailGcd D (finiteScalarGcd D H) ∧ H < 2 * D ^ 2 := by
  exact quadratic_scalar_tail_gcd hD hp (by omega) hpD
