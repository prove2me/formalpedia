-- Prove2me | Definitions.Def_ErdosProblems_Erdos243_GlobalLcmHeight
-- name    : ErdosProblems_Erdos243_GlobalLcmHeight
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T21:26:56.274047+00:00
-- url     : https://prove2.me/theorems/d96a5330-38ac-42a3-a3db-85bda166d99f
-- title:
--   Cumulative LCM and overlap debt
-- statement:
--   For a natural initial denominator q and natural digits a_n, defines L_0=q and L_(n+1)=lcm(L_n,a_n), D_0=q and D_(n+1)=a_n D_n, and M_0=1 and M_(n+1)=M_n gcd(L_n,a_n). Included identities give M_n L_n=D_n. The initial denominator is part of these coordinates.
-- source:
--   Pinned original Lean source: https://github.com/wcook04/plectis-erdos-lean/blob/fbf41fb8b571d217b1648070dcc39d5eda5394ad/ErdosProblems/Erdos243/GlobalLcmHeight.lean#L1-L152
--   Paper context and prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/243/erdos-243-reciprocal-tail-rigidity.tex#L1151-L1235
--   AI-assisted formalization and editorial review; no human review attested. Hosted import name ErdosProblems_Erdos243_GlobalLcmHeight is the versioned native alias of original module ErdosProblems.Erdos243.GlobalLcmHeight.

import Definitions.Def_ErdosProblems_Erdos243_ReciprocalTailRigidity
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fin.Pigeonhole
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.Ring

/-!
# Erdős #243: cumulative-LCM height

Global coordinates which retain digit-overlap payments that can disappear
from the dynamically reduced numerator-denominator pair.
-/

namespace ErdosProblems.Erdos243

/-- Cumulative least common multiple of the initial denominator and all
digits strictly before `n`. -/
def cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => Nat.lcm (cumulativeDigitLcm q a n) (a n)

@[simp]
theorem cumulativeDigitLcm_zero (q : ℕ) (a : ℕ → ℕ) :
    cumulativeDigitLcm q a 0 = q := rfl

@[simp]
theorem cumulativeDigitLcm_succ (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    cumulativeDigitLcm q a (n + 1) =
      Nat.lcm (cumulativeDigitLcm q a n) (a n) := rfl

/-- Product-cleared denominator scale through the first `n` digits. -/
def digitProductScale (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => a n * digitProductScale q a n

/-- Cumulative product of the irreversible LCM-overlap payments. -/
def cumulativeOverlapDebt (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      cumulativeOverlapDebt q a n *
        Nat.gcd (cumulativeDigitLcm q a n) (a n)

/-- Global overlap is relocation rather than erasure: at every finite
horizon, overlap debt times the cumulative LCM is exactly the full
product-cleared digit scale. -/
theorem cumulativeOverlapDebt_mul_lcm_eq_productScale
    (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
    cumulativeOverlapDebt q a n * cumulativeDigitLcm q a n =
      digitProductScale q a n := by
  induction n with
  | zero =>
      simp [cumulativeOverlapDebt, cumulativeDigitLcm, digitProductScale]
  | succ n ih =>
      simp only [cumulativeOverlapDebt, cumulativeDigitLcm, digitProductScale]
      calc
        (cumulativeOverlapDebt q a n *
              Nat.gcd (cumulativeDigitLcm q a n) (a n)) *
            Nat.lcm (cumulativeDigitLcm q a n) (a n) =
          cumulativeOverlapDebt q a n *
            (Nat.gcd (cumulativeDigitLcm q a n) (a n) *
              Nat.lcm (cumulativeDigitLcm q a n) (a n)) := by ring
        _ = cumulativeOverlapDebt q a n *
              (cumulativeDigitLcm q a n * a n) := by
            rw [Nat.gcd_mul_lcm]
        _ = (cumulativeOverlapDebt q a n *
              cumulativeDigitLcm q a n) * a n := by ring
        _ = digitProductScale q a n * a n := by rw [ih]
        _ = a n * digitProductScale q a n := by ring















end ErdosProblems.Erdos243


