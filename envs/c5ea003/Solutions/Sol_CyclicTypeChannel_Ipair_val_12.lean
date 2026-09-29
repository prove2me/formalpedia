-- Prove2me | solution 1 for CyclicTypeChannel.Ipair_val_12
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:05:40.729316+00:00
-- url     : https://prove2.me/submissions/4d436ce0-198b-426d-a085-a83d9fa4e822

-- Sol generated from Shared/CyclicTypeChannelValues.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_Ipair_eq
import Theorems.Thm_CyclicTypeChannel_condPairEntropy_val_12
import Theorems.Thm_CyclicTypeChannel_lb_144
import Theorems.Thm_CyclicTypeChannel_lb_16
import Theorems.Thm_CyclicTypeChannel_lb_4
import Theorems.Thm_CyclicTypeChannel_lb_8
import Theorems.Thm_CyclicTypeChannel_uEnt_eq_countSum
import Theorems.Thm_CyclicTypeChannel_lb_10
import Theorems.Thm_CyclicTypeChannel_lb_100
import Theorems.Thm_CyclicTypeChannel_lb_12
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


/-- Exact entropy of the unordered type pair of a `C12` semiprime. -/
theorem pairEntropy_val_12 : pairEntropy 12 = (7/8 : ℝ) + (2 : ℝ) * Real.logb 2 3 := by
  have h : ((CyclicTypeChannel.box 12).image (typePair 12)).val.map
      (fun v => (#{q ∈ CyclicTypeChannel.box 12 | typePair 12 q = v} : ℕ)) = (↑[1, 1, 2, 4, 4, 4, 4, 4, 4, 4, 4, 4, 8, 8, 8, 8, 8, 16, 16, 16, 16] : Multiset ℕ) := by decide
  rw [pairEntropy, uEnt_eq_countSum _ _ _ h, show (CyclicTypeChannel.box 12).card = 144 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]
  ring



/-! ### The `C16` channel: `Q(ζ_17)` -/






open CyclicTypeChannel in
theorem solution: Ipair 12 = (5/36 : ℝ) + (1 : ℝ) * Real.logb 2 3 := by
  rw [Ipair_eq, pairEntropy_val_12, condPairEntropy_val_12]
  ring
