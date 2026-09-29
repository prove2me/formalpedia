-- Prove2me | solution 1 for CyclicTypeChannel.condPairEntropy_val_5
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:22:56.400143+00:00
-- url     : https://prove2.me/submissions/58f2a4fa-ece8-48d4-8c1b-67fb49a9e7b7

-- Sol generated from Shared/CyclicTypeChannelCRT.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelCRTLaw
import Theorems.Thm_CyclicTypeChannel_lb_4
import Theorems.Thm_CyclicTypeChannel_uEnt_eq_countSum
import Theorems.Thm_CyclicTypeChannel_lb_10
import Theorems.Thm_CyclicTypeChannel_lb_100
import Theorems.Thm_CyclicTypeChannel_lb_12
import Theorems.Thm_CyclicTypeChannel_lb_144
import Theorems.Thm_CyclicTypeChannel_lb_15
import Theorems.Thm_CyclicTypeChannel_lb_16
import Theorems.Thm_CyclicTypeChannel_lb_225
import Theorems.Thm_CyclicTypeChannel_lb_24
import Theorems.Thm_CyclicTypeChannel_lb_25
import Theorems.Thm_CyclicTypeChannel_lb_256
import Theorems.Thm_CyclicTypeChannel_lb_32
import Theorems.Thm_CyclicTypeChannel_lb_36
import Theorems.Thm_CyclicTypeChannel_lb_6
import Theorems.Thm_CyclicTypeChannel_lb_64
import Theorems.Thm_CyclicTypeChannel_lb_8
import Theorems.Thm_CyclicTypeChannel_lb_81
import Theorems.Thm_CyclicTypeChannel_lb_9
/-
# CRT additivity of the cyclic type-pair channel

This file extends the exact-value catalogue of the cyclic type-pair channel to
the orders `n ∈ {3, 5, 8, 9, 15}` and proves the two structural laws that the
extended table makes visible.

* **CRT additivity.**  For coprime cyclic orders the type-pair information is
  *exactly additive*:
  `Ipair (n₁ * n₂) = Ipair n₁ + Ipair n₂` whenever `gcd n₁ n₂ = 1`
  (verified here for the pairs `(2,3)`, `(2,5)`, `(4,3)`, `(3,5)`).
  This is the information-theoretic shadow of the CRT decomposition of a cyclic
  group into its primary components.

* **Evenness, not compositeness, breaks the one-bit cap.**  The order `8` is a
  further above-cap example (`21/16 > 1`), while *every* odd order computed here
  (`3, 5, 9, 15`) sits strictly *below* one bit.  So the mechanism which pushes
  the multi-state type channel above the binary-fork cap is the presence of the
  order-two element (the quadratic character), amplified by the remaining
  divisor structure.
-/

open CyclicTypeChannel

open Finset

set_option maxRecDepth 100000

/-! ### The abstract cyclic order `C3` -/





/-! ### The abstract cyclic order `C5` -/





/-! ### The abstract cyclic order `C8` -/





/-! ### The abstract cyclic order `C9` -/





/-! ### The abstract cyclic order `C15` -/





/-! ### CRT additivity of the type-pair information

For coprime cyclic orders the information carried by the unordered type pair of
a semiprime splits as a sum over the primary components. -/





/-! ### Evenness, not compositeness, is what breaks the cap -/








/-! ### A value beyond the reach of enumeration

`n = 60` has a sample CyclicTypeChannel.box of `3600` pairs, out of reach of direct kernel
enumeration; the CRT law computes it from the primary parts `4` and `15`. -/




open CyclicTypeChannel in
theorem solution: condPairEntropy 5 = (-16/25 : ℝ) + (-12/25 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
  have himg : (CyclicTypeChannel.box 5).image (prodRes 5) = range 5 := by decide
  have e0 : uEnt {x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 0} (typePair 5) = (-8/5 : ℝ) + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 0}).image (typePair 5)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 0} | typePair 5 q = v} : ℕ))
        = (↑[1, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 0}) = 5 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e1 : uEnt {x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 1} (typePair 5) = (-2/5 : ℝ) + (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 1}).image (typePair 5)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 1} | typePair 5 q = v} : ℕ))
        = (↑[2, 3] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 1}) = 5 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e2 : uEnt {x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 2} (typePair 5) = (-2/5 : ℝ) + (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 2}).image (typePair 5)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 2} | typePair 5 q = v} : ℕ))
        = (↑[2, 3] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 2}) = 5 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e3 : uEnt {x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 3} (typePair 5) = (-2/5 : ℝ) + (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 3}).image (typePair 5)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 3} | typePair 5 q = v} : ℕ))
        = (↑[2, 3] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 3}) = 5 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  have e4 : uEnt {x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 4} (typePair 5) = (-2/5 : ℝ) + (-3/5 : ℝ) * Real.logb 2 3 + (1 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 4}).image (typePair 5)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 4} | typePair 5 q = v} : ℕ))
        = (↑[2, 3] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 4}) = 5 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
    ring
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2, e3, e4]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256, show (CyclicTypeChannel.box 5).card = 25 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 0}) = 5 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 1}) = 5 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 2}) = 5 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 3}) = 5 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 5 | prodRes 5 x = 4}) = 5 from by decide]
  ring
