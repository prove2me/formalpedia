-- Prove2me | solution 1 for CyclicTypeChannel.condPairEntropy_val_8
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:16:09.328233+00:00
-- url     : https://prove2.me/submissions/fadc9ada-fc3f-47af-9192-cc346d415ec9

-- Sol generated from Shared/CyclicTypeChannelCRT.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelCRTLaw
import Theorems.Thm_CyclicTypeChannel_lb_4
import Theorems.Thm_CyclicTypeChannel_lb_8
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
theorem solution: condPairEntropy 8 = (49/32 : ℝ) := by
  have himg : (CyclicTypeChannel.box 8).image (prodRes 8) = range 8 := by decide
  have e0 : uEnt {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 0} (typePair 8) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 0}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 0} | typePair 8 q = v} : ℕ))
        = (↑[1, 1, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 0}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e1 : uEnt {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 1} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 1}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 1} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 1}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e2 : uEnt {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 2} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 2}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 2} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 2}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e3 : uEnt {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 3} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 3}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 3} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 3}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e4 : uEnt {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 4} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 4}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 4} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 4}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e5 : uEnt {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 5} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 5}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 5} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 5}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e6 : uEnt {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 6} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 6}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 6} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 6}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  have e7 : uEnt {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 7} (typePair 8) = (3/2 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 7}).image (typePair 8)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 7} | typePair 8 q = v} : ℕ))
        = (↑[2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 7}) = 8 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256]
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2, e3, e4, e5, e6, e7]
  norm_num [lb_4, lb_6, lb_8, lb_9, lb_10, lb_12, lb_15, lb_16, lb_24, lb_25, lb_32, lb_36, lb_64, lb_81, lb_100, lb_144, lb_225, lb_256, show (CyclicTypeChannel.box 8).card = 64 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 0}) = 8 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 1}) = 8 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 2}) = 8 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 3}) = 8 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 4}) = 8 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 5}) = 8 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 6}) = 8 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 8 | prodRes 8 x = 7}) = 8 from by decide]
