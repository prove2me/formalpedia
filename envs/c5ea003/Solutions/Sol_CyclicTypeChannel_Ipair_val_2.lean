-- Prove2me | solution 1 for CyclicTypeChannel.Ipair_val_2
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:07:22.63769+00:00
-- url     : https://prove2.me/submissions/90c27b1e-5b5b-4c2d-aa0d-ce9b291a1f85

-- Sol generated from Shared/CyclicTypeChannelValues.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_Ipair_eq
import Theorems.Thm_CyclicTypeChannel_condPairEntropy_val_2
import Theorems.Thm_CyclicTypeChannel_lb_4
import Theorems.Thm_CyclicTypeChannel_uEnt_eq_countSum
import Theorems.Thm_CyclicTypeChannel_lb_10
import Theorems.Thm_CyclicTypeChannel_lb_100
import Theorems.Thm_CyclicTypeChannel_lb_12
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


/-- Exact entropy of the unordered type pair of a `C2` semiprime. -/
theorem pairEntropy_val_2 : pairEntropy 2 = (3/2 : ℝ) := by
  have h : ((CyclicTypeChannel.box 2).image (typePair 2)).val.map
      (fun v => (#{q ∈ CyclicTypeChannel.box 2 | typePair 2 q = v} : ℕ)) = (↑[1, 1, 2] : Multiset ℕ) := by decide
  rw [pairEntropy, uEnt_eq_countSum _ _ _ h, show (CyclicTypeChannel.box 2).card = 4 from by decide]
  norm_num [lb_4, lb_6, lb_8, lb_10, lb_12, lb_16, lb_32, lb_36, lb_64, lb_100, lb_144, lb_256]



/-! ### The `C4` channel: `Q(ζ_5)` -/





/-! ### The `C6` channel: `Q(ζ_7)` -/





/-! ### The `C10` channel: `Q(ζ_11)` -/





/-! ### The `C12` channel: `Q(ζ_13)` -/





/-! ### The `C16` channel: `Q(ζ_17)` -/






open CyclicTypeChannel in
theorem solution: Ipair 2 = (1 : ℝ) := by
  rw [Ipair_eq, pairEntropy_val_2, condPairEntropy_val_2]
  ring
