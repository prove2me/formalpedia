-- Prove2me | solution 1 for CyclicTypeChannel.condPairEntropy_val_12
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:03:49.371241+00:00
-- url     : https://prove2.me/submissions/cad6c515-2436-4166-b86c-3c9a646385ad

-- Sol generated from Shared/CyclicTypeChannelValues.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_lb_12
import Theorems.Thm_CyclicTypeChannel_lb_4
import Theorems.Thm_CyclicTypeChannel_uEnt_eq_countSum
import Theorems.Thm_CyclicTypeChannel_lb_10
import Theorems.Thm_CyclicTypeChannel_lb_100
import Theorems.Thm_CyclicTypeChannel_lb_144
import Theorems.Thm_CyclicTypeChannel_lb_16
import Theorems.Thm_CyclicTypeChannel_lb_256
import Theorems.Thm_CyclicTypeChannel_lb_32
import Theorems.Thm_CyclicTypeChannel_lb_36
import Theorems.Thm_CyclicTypeChannel_lb_6
import Theorems.Thm_CyclicTypeChannel_lb_64
import Theorems.Thm_CyclicTypeChannel_lb_8
/-
# Exact values of the cyclic splitting-type channel

Exact, closed-form evaluations of the type channel `H(T)`, the semiprime
type-pair entropy `H(Π)`, the conditional entropy `H(Π | N mod f)` and the
type-pair channel `I_pair = H(Π) - (1/φ(f)) ∑_c H(Π_c)` for the cyclic groups
`C₂, C₄, C₆, C₁₀, C₁₂, C₁₆`, i.e. for the cyclotomic fields
`Q(ζ₃), Q(ζ₅), Q(ζ₇), Q(ζ₁₁), Q(ζ₁₃), Q(ζ₁₇)`.

Every value is obtained from the count form `uEnt_eq_countSum` of the entropy
together with a kernel-checked enumeration of the fibre cardinalities over the
unit group.
-/

open CyclicTypeChannel

open Finset

set_option maxRecDepth 100000

/-! ### The `C2` channel: `Q(ζ_3)` -/





/-! ### The `C4` channel: `Q(ζ_5)` -/





/-! ### The `C6` channel: `Q(ζ_7)` -/





/-! ### The `C10` channel: `Q(ζ_11)` -/





/-! ### The `C12` channel: `Q(ζ_13)` -/





/-! ### The `C16` channel: `Q(ζ_17)` -/






open CyclicTypeChannel in
theorem solution: condPairEntropy 12 = (53/72 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
  have himg : (CyclicTypeChannel.box 12).image (prodRes 12) = range 12 := by decide
  have e0 : uEnt {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 0} (typePair 12) = (5/6 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 0}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 0} | typePair 12 q = v} : ℕ))
        = (↑[1, 1, 2, 2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 0}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e1 : uEnt {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 1} (typePair 12) = (1 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 1}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 1} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 2, 2, 2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 1}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e2 : uEnt {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 2} (typePair 12) = (2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 2}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 2} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 2}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e3 : uEnt {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 3} (typePair 12) = (1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 3}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 3} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 4, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 3}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e4 : uEnt {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 4} (typePair 12) = (5/6 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 4}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 4} | typePair 12 q = v} : ℕ))
        = (↑[1, 1, 2, 2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 4}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e5 : uEnt {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 5} (typePair 12) = (1 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 5}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 5} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 2, 2, 2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 5}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e6 : uEnt {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 6} (typePair 12) = (1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 6}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 6} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 4, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 6}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e7 : uEnt {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 7} (typePair 12) = (1 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 7}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 7} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 2, 2, 2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 7}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e8 : uEnt {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 8} (typePair 12) = (5/6 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 8}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 8} | typePair 12 q = v} : ℕ))
        = (↑[1, 1, 2, 2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 8}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e9 : uEnt {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 9} (typePair 12) = (1/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 9}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 9} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 4, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 9}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e10 : uEnt {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 10} (typePair 12) = (2/3 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 10}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 10} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 2, 2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 10}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  have e11 : uEnt {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 11} (typePair 12) = (1 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 11}).image (typePair 12)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 11} | typePair 12 q = v} : ℕ))
        = (↑[2, 2, 2, 2, 2, 2] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 11}) = 12 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
    ring
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256, show (CyclicTypeChannel.box 12).card = 144 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 0}) = 12 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 1}) = 12 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 2}) = 12 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 3}) = 12 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 4}) = 12 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 5}) = 12 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 6}) = 12 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 7}) = 12 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 8}) = 12 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 9}) = 12 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 10}) = 12 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 12 | prodRes 12 x = 11}) = 12 from by decide]
  ring
