-- Prove2me | solution 1 for CyclicTypeChannel.condSProjEntropy_val_6
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:22:58.533457+00:00
-- url     : https://prove2.me/submissions/b0b97489-6449-4aff-a6e7-a9692f281a1f

-- Sol generated from Shared/CyclicTypeChannelCap.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_lb_4
import Theorems.Thm_CyclicTypeChannel_lb_6
import Theorems.Thm_CyclicTypeChannel_uEnt_eq_countSum
/-
# Breaking the one-bit binary-fork cap

The symmetric semiprime forks previously studied are *binary* read-outs, and a
binary symmetric fork carries at most one bit.  The splitting type of a cyclic
field is **multi-state**, and this file proves that its type-pair channel
strictly exceeds the one-bit cap for every cyclic order `n ∈ {4,6,10,12,16}`,
while the quadratic case `n = 2` sits exactly at the cap.

It also proves the two *lossiness* statements that isolate the type as the
complete object:

* the root-count read-out (`splits completely?`) is a strictly coarser channel
  than the full type, already at `n = 4` and `n = 6`;
* the split-count `s`-projection of a semiprime type pair carries strictly less
  than the full type pair.
-/

open CyclicTypeChannel

open Finset

set_option maxRecDepth 100000

/-! ## 1. The type-pair channel exceeds one bit -/









/-! ## 2. The root-count read-out is strictly lossy -/





/-! ## 3. The split-count `s`-projection is strictly lossy -/











open CyclicTypeChannel in
theorem solution:
    condEnt (CyclicTypeChannel.box 6) (sProj ∘ typePair 6) (prodRes 6)
      = -(7 / 18 : ℝ) + Real.logb 2 3 - (5 / 36 : ℝ) * Real.logb 2 5 := by
  have himg : (CyclicTypeChannel.box 6).image (prodRes 6) = range 6 := by decide
  have e0 : uEnt {x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 0} (sProj ∘ typePair 6)
      = 1 + Real.logb 2 3 - (5 / 6 : ℝ) * Real.logb 2 5 := by
    have h : (({x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 0}).image (sProj ∘ typePair 6)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 0} | (sProj ∘ typePair 6) q = v} : ℕ))
        = (↑[1, 5] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h, show (#{x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 0}) = 6 from by decide]
    norm_num [lb_6]
    ring
  have e1 : uEnt {x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 1} (sProj ∘ typePair 6)
      = -(2 / 3 : ℝ) + Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 1}).image (sProj ∘ typePair 6)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 1} | (sProj ∘ typePair 6) q = v} : ℕ))
        = (↑[2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h, show (#{x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 1}) = 6 from by decide]
    norm_num [lb_6, lb_4]
    ring
  have e2 : uEnt {x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 2} (sProj ∘ typePair 6)
      = -(2 / 3 : ℝ) + Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 2}).image (sProj ∘ typePair 6)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 2} | (sProj ∘ typePair 6) q = v} : ℕ))
        = (↑[2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h, show (#{x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 2}) = 6 from by decide]
    norm_num [lb_6, lb_4]
    ring
  have e3 : uEnt {x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 3} (sProj ∘ typePair 6)
      = -(2 / 3 : ℝ) + Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 3}).image (sProj ∘ typePair 6)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 3} | (sProj ∘ typePair 6) q = v} : ℕ))
        = (↑[2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h, show (#{x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 3}) = 6 from by decide]
    norm_num [lb_6, lb_4]
    ring
  have e4 : uEnt {x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 4} (sProj ∘ typePair 6)
      = -(2 / 3 : ℝ) + Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 4}).image (sProj ∘ typePair 6)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 4} | (sProj ∘ typePair 6) q = v} : ℕ))
        = (↑[2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h, show (#{x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 4}) = 6 from by decide]
    norm_num [lb_6, lb_4]
    ring
  have e5 : uEnt {x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 5} (sProj ∘ typePair 6)
      = -(2 / 3 : ℝ) + Real.logb 2 3 := by
    have h : (({x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 5}).image (sProj ∘ typePair 6)).val.map
        (fun v => (#{q ∈ {x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 5} | (sProj ∘ typePair 6) q = v} : ℕ))
        = (↑[2, 4] : Multiset ℕ) := by decide
    rw [uEnt_eq_countSum _ _ _ h, show (#{x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 5}) = 6 from by decide]
    norm_num [lb_6, lb_4]
    ring
  rw [condEnt, himg, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one, e0, e1, e2, e3, e4, e5]
  norm_num [show (CyclicTypeChannel.box 6).card = 36 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 0}) = 6 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 1}) = 6 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 2}) = 6 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 3}) = 6 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 4}) = 6 from by decide,
    show (#{x ∈ CyclicTypeChannel.box 6 | prodRes 6 x = 5}) = 6 from by decide]
  ring
