-- Prove2me | solution 1 for CyclicTypeChannel.logb_sub_logb_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T21:45:56.931762+00:00
-- url     : https://prove2.me/submissions/2e09cdfe-e7da-481e-ab49-89b5a3c401a8

-- Sol generated from Shared/CyclicTypeChannelPrime.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannelPrime
/-
# The prime cyclic order: a closed form for the type-pair channel

The exact-value files compute the type-pair channel `Ipair n` for a finite list of
cyclic orders.  This file closes the *prime* case in complete generality: for
every prime `p` the channel of the cyclic order `C p` is

  `Ipair p = log₂ p - (p-1)(2p-1)/p² · log₂ (p-1) + (p-1)(p-2)/p² · log₂ (p-2)`.

(`Ipair_prime`; the two exact values `Ipair 3` and `Ipair 5` recorded in
`CyclicTypeChannelCRT.lean` are the instances `p = 3, 5`.)

Two consequences:

* `Ipair_prime_lt_one`: every **odd** prime order is *strictly below* the one-bit
  binary-fork cap, so among prime cyclic orders the cap is attained exactly at
  `p = 2` (`Ipair_prime_eq_one_iff`).  This upgrades the isolated computations
  `Ipair 3 < 1`, `Ipair 5 < 1` to an infinite statement and shows that the
  above-cap phenomenon of `C₄, C₆, C₁₀, C₁₂, C₁₆` is genuinely a *composite*
  phenomenon: a prime cyclic order has only two splitting types, and its fork is
  exactly the binary fork that papers 72–74 capped.
* `above_cap_imp_not_prime`: breaking the cap forces the cyclic order to be
  composite.
-/

open CyclicTypeChannel

open Finset

/-! ## 1. The splitting type of a prime cyclic order -/





/-! ## 2. The three fibres in the CyclicTypeChannel.box -/











/-! ## 3. The pair entropy -/



/-! ## 4. The conditional entropy -/











/-! ### The nonzero fibres -/









/-! ## 5. Consequences: the cap among prime orders -/







/-! ## 6. Cross-checks against the enumerated values

`Ipair 3` and `Ipair 5` were computed in `CyclicTypeChannelCRT.lean` by explicit
enumeration of the `9`- and `25`-element boxes.  Re-deriving them from the general
prime formula is an independent check of the closed form. -/




open CyclicTypeChannel in
lemma solution{x : ℝ} (hx : 1 ≤ x) :
    Real.logb 2 (x + 1) - Real.logb 2 x ≤ 1 / (x * Real.log 2) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h : Real.log (x + 1) - Real.log x = Real.log ((x + 1) / x) := by
    rw [Real.log_div (by linarith) (ne_of_gt hx0)]
  have hle : Real.log ((x + 1) / x) ≤ 1 / x := by
    have h2 := Real.log_le_sub_one_of_pos (x := (x + 1) / x) (by positivity)
    have hsimp : (x + 1) / x - 1 = 1 / x := by field_simp; ring
    rw [hsimp] at h2
    exact h2
  have hgoal : Real.log ((x + 1) / x) / Real.log 2 ≤ (1 / x) / Real.log 2 := by
    gcongr
  rw [Real.logb, Real.logb, div_sub_div_same, h]
  calc Real.log ((x + 1) / x) / Real.log 2 ≤ (1 / x) / Real.log 2 := hgoal
    _ = 1 / (x * Real.log 2) := by field_simp
