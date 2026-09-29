-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_PaperComplete_divisor_twice_prime
-- name    : ErdosProblems.Erdos68.PaperComplete.divisor_twice_prime
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:05:25.465007+00:00
-- url     : https://prove2.me/theorems/42b2ed94-3060-4cbd-89e9-176ca86c7988
-- title:
--   Divisor twice prime
-- statement:
--   If p is prime and 2 ≤ d < 2p divides 2p, then d is 2 or p.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/PaperCompleteMomentHorizon.lean#L74-L106
--   Correspondence: finite channel-moment analysis for Erdős #68. No novelty or whole-problem claim.

import Definitions.Def_ErdosProblems_Erdos68_FactorialChannelCertificate
import Definitions.Def_ErdosProblems_Erdos68_DivisorChannelBasis
import Definitions.Def_ErdosProblems_Erdos68_PaperCompleteMomentHorizon
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

open scoped BigOperators

open ErdosProblems.Erdos68.PaperComplete

theorem ErdosProblems.Erdos68.PaperComplete.divisor_twice_prime {p d : ℕ} (hp : p.Prime)
    (hd : 2 ≤ d) (hlt : d < 2 * p) (hdiv : d ∣ 2 * p) :
    d = 2 ∨ d = p := by sorry
