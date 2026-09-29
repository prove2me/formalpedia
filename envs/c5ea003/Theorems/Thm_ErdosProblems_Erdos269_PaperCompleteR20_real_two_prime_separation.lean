-- Prove2me | Theorems.Thm_ErdosProblems_Erdos269_PaperCompleteR20_real_two_prime_separation
-- name    : ErdosProblems.Erdos269.PaperCompleteR20.real_two_prime_separation
-- status  : Proved
-- author  : @willcook
-- created : 2026-09-27T22:43:01.584993+00:00
-- url     : https://prove2.me/theorems/d17dc6c2-5088-4ec5-acc7-d27a68f9f240
-- title:
--   Real two prime separation
-- statement:
--   For any real bases p,q > 1, the two-prime kernel factors into a function of i times a function of j. Consequently every two-by-two minor of its matrix of values is zero.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/PaperCompleteR20/RealTwoPrimeKernel.lean#L62-L71
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Definitions.Def_ErdosProblems_Erdos269_PaperCompleteR20_RealTwoPrimeKernel
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Two-generator separation for arbitrary real bases

The long paper allows real generators greater than one. Integer floors and
integer powers retain that literal domain, including nonintegral bases.
-/


noncomputable section

open ErdosProblems.Erdos269.PaperCompleteR20

theorem ErdosProblems.Erdos269.PaperCompleteR20.real_two_prime_separation {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    (∀ i j : ℕ, realTwoPrimeKernel p q i j =
      (p ^ i * q ^ ⌊Real.logb q (p ^ i)⌋)⁻¹ *
        (p ^ ⌊Real.logb p (q ^ j)⌋ * q ^ j)⁻¹) ∧
    (∀ i i' j j' : ℕ,
      realTwoPrimeKernel p q i j * realTwoPrimeKernel p q i' j' -
        realTwoPrimeKernel p q i j' * realTwoPrimeKernel p q i' j = 0) := by sorry
