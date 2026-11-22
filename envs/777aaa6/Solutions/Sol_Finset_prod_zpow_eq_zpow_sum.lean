-- Prove2me | solution 1 for Finset.prod_zpow_eq_zpow_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:54:13.465885+00:00
-- url     : https://prove2.me/submissions/66c907a9-5297-4645-9cb4-3c79879060cf

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
import Definitions.Def_BruhatTits_Utils_Misc

set_option autoImplicit false
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
open Finset
variable {ι α β : Type*} [CommGroupWithZero β]
namespace Finset
theorem _root_.solution (s : Finset ι) (f : ι → ℤ) (a : β) (ha : a ≠ 0):
    ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i :=
  cons_induction (by simp) (fun _ _ _ h ↦ by simp [h, zpow_add₀ ha]) s
end Finset
