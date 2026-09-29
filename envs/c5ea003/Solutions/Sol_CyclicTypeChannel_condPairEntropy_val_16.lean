-- Prove2me | solution 1 for CyclicTypeChannel.condPairEntropy_val_16
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:05:41.370508+00:00
-- url     : https://prove2.me/submissions/80566177-e124-4113-a4e1-32faec6a8471

-- Sol generated from Shared/CyclicTypeChannelValues.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_lb_16
import Theorems.Thm_CyclicTypeChannel_lb_4
import Theorems.Thm_CyclicTypeChannel_lb_8
import Theorems.Thm_CyclicTypeChannel_uEnt_eq_countSum
import Theorems.Thm_CyclicTypeChannel_lb_10
import Theorems.Thm_CyclicTypeChannel_lb_100
import Theorems.Thm_CyclicTypeChannel_lb_12
import Theorems.Thm_CyclicTypeChannel_lb_144
import Theorems.Thm_CyclicTypeChannel_lb_256
import Theorems.Thm_CyclicTypeChannel_lb_32
import Theorems.Thm_CyclicTypeChannel_lb_36
import Theorems.Thm_CyclicTypeChannel_lb_6
import Theorems.Thm_CyclicTypeChannel_lb_64
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
theorem solution: condPairEntropy 16 = (225/128 : ℝ) := by
  have himg : (CyclicTypeChannel.box 16).image (prodRes 16) = range 16 := by decide
  have e0 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 0} (typePair 16) = (15/8 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 0}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 0} | typePair 16 q = v} : ℕ))
        = (↑[1, 1, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 0}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e1 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 1} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 1}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 1} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 1}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e2 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 2} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 2}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 2} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 2}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e3 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 3} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 3}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 3} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 3}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e4 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 4} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 4}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 4} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 4}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e5 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 5} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 5}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 5} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 5}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e6 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 6} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 6}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 6} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 6}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e7 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 7} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 7}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 7} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 7}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e8 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 8} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 8}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 8} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 8}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e9 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 9} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 9}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 9} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 9}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e10 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 10} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 10}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 10} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 10}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e11 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 11} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 11}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 11} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 11}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e12 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 12} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 12}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 12} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 12}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e13 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 13} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 13}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 13} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 13}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e14 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 14} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 14}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 14} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 14}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  have e15 : uEnt {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 15} (typePair 16) = (7/4 : ℝ) := by
    have h : (({x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 15}).image (typePair 16)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 15} | typePair 16 q = v} : ℕ))
        = (↑[2, 2, 4, 8] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h,
      show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 15}) = 16 from by decide]
    norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  rw [condPairEntropy, condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one,
    e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256, show (CyclicTypeChannel.box 16).card = 256 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 0}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 1}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 2}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 3}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 4}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 5}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 6}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 7}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 8}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 9}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 10}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 11}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 12}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 13}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 14}) = 16 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 16 | prodRes 16 x = 15}) = 16 from by decide]
