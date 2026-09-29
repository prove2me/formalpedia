-- Prove2me | solution 1 for ErdosProblems.Erdos68.factorialMoment_single
-- status  : ACCEPTED   (prove)
-- author  : @willcook
-- created : 2026-09-27T16:04:15.344589+00:00
-- url     : https://prove2.me/submissions/6c64e036-55d7-4a27-91e3-165894a7776c

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

namespace ErdosProblems.Erdos68
open Finsupp

/-! ## Linearity of the Finsupp channel presentation -/
end ErdosProblems.Erdos68

open Finsupp
open ErdosProblems in
open ErdosProblems.Erdos68 in
theorem solution (i : ℕ) (z : ℤ) :
    factorialMoment (single i z) = z * (i.factorial : ℤ) := by
  unfold factorialMoment
  exact sum_single_index (by simp)
