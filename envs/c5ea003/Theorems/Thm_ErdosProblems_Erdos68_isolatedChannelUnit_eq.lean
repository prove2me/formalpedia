-- Prove2me | Theorems.Thm_ErdosProblems_Erdos68_isolatedChannelUnit_eq
-- name    : ErdosProblems.Erdos68.isolatedChannelUnit_eq
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T16:03:19.12502+00:00
-- url     : https://prove2.me/theorems/a2b6d52e-3bf9-48ed-b635-63e26062f85e
-- title:
--   Isolated Channel Unit eq
-- statement:
--   The isolated channel unit is zero for indices at most one and otherwise satisfies the adjacent-difference recursion with corrections from proper divisor channels.
-- source:
--   Pinned Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fcb1eff5111efabc25fcf3dfcd6ec48d42ef345c/ErdosProblems/Erdos68/DivisorChannelBasis.lean#L537-L547
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

















/-! ## Support-sensitive factor of `12` -/

















/-! ## Channel moduli and `12 L_D` -/





















/-! ## Isolated channel units `U_n` -/

open ErdosProblems.Erdos68

theorem ErdosProblems.Erdos68.isolatedChannelUnit_eq (n : ℕ) :
    isolatedChannelUnit n =
      if n ≤ 1 then 0
      else
        adjacentDifference n -
          ∑ d ∈ (Finset.Ico 2 n).attach,
            if d.1 ∣ n then
              (channelWeight n d.1 : ℤ) • isolatedChannelUnit d.1
            else 0 := by sorry
