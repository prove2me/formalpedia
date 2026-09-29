-- Prove2me | solution 1 for ForkPinning.mutualInfo_le_entropy
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-19T05:22:00.088719+00:00
-- url     : https://prove2.me/submissions/ab2c1464-6028-4656-837e-61e96d701b38

import Mathlib
import Definitions.Def_Probability_ForkPinningCore

open ForkPinning Finset Real
set_option autoImplicit false

/- Attributed proof port: Paul Klemstine, Aether Catalog, commit 53c2925a02,
   Catalog/Probability/ForkPinningCore.lean. Helpers come from lines75–166;
   final result from255–258. The probability nonnegativity helper also covers
   the empty sample type; the final theorem retains the server target's arity. -/

namespace ForkPinningEntropyPort

variable {Ω : Type*} [Fintype Ω]
variable {κ β : Type*} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]

theorem prb_nonneg (X : Ω → κ) (k : κ) : 0 ≤ prb X k := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

lemma fiber_joint (X : Ω → κ) (Y : Ω → β) (k : κ) (b : β) :
    fiber (joint X Y) (k, b) = (fiber X k).filter (fun ω => Y ω = b) := by
  ext ω; simp [fiber, joint, Prod.ext_iff]

lemma sum_prb_joint (X : Ω → κ) (Y : Ω → β) (k : κ) :
    ∑ b : β, prb (joint X Y) (k, b) = prb X k := by
  simp only [prb, fiber_joint]
  rw [← Finset.sum_div]
  congr 1
  have := Finset.card_eq_sum_card_fiberwise
    (f := Y) (s := fiber X k) (t := (univ : Finset β)) (by intro x _; exact mem_univ _)
  exact_mod_cast this.symm

lemma negMulLog_sum_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    negMulLog (∑ i ∈ s, f i) = ∑ i ∈ s, -(f i) * Real.log (∑ i ∈ s, f i) := by
  set S := ∑ i ∈ s, f i with hS
  simp only [neg_mul]
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul, ← hS, negMulLog, neg_mul]

lemma negMulLog_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i) :
    negMulLog (∑ i ∈ s, f i) ≤ ∑ i ∈ s, negMulLog (f i) := by
  set S := ∑ i ∈ s, f i with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg hf
  rcases eq_or_lt_of_le hS0 with h | h
  · -- degenerate case: every term vanishes
    have hzero : ∀ i ∈ s, f i = 0 := fun i hi =>
      (Finset.sum_eq_zero_iff_of_nonneg hf).mp h.symm i hi
    rw [← h, negMulLog_zero,
      Finset.sum_congr rfl (fun i hi => by rw [hzero i hi, negMulLog_zero])]
    simp
  · have key : ∀ i ∈ s, -(f i) * Real.log S ≤ negMulLog (f i) := by
      intro i hi
      rcases eq_or_lt_of_le (hf i hi) with h0 | h0
      · simp [negMulLog, ← h0]
      · have hle : f i ≤ S := Finset.single_le_sum hf hi
        have : Real.log (f i) ≤ Real.log S := Real.log_le_log h0 hle
        unfold negMulLog
        nlinarith
    calc negMulLog S = ∑ i ∈ s, -(f i) * Real.log S := by rw [hS, ← negMulLog_sum_eq]
      _ ≤ ∑ i ∈ s, negMulLog (f i) := Finset.sum_le_sum key

lemma entropy_joint_eq (X : Ω → κ) (Y : Ω → β) :
    H (joint X Y) = ∑ k : κ, ∑ b : β, negMulLog (prb (joint X Y) (k, b)) := by
  unfold H
  rw [Fintype.sum_prod_type]

theorem entropy_le_entropy_joint (X : Ω → κ) (Y : Ω → β) : H X ≤ H (joint X Y) := by
  rw [entropy_joint_eq]
  unfold H
  refine Finset.sum_le_sum ?_
  intro k _
  have := negMulLog_sum_le (univ : Finset β) (fun b => prb (joint X Y) (k, b))
    (fun b _ => prb_nonneg _ _)
  rwa [sum_prb_joint X Y k] at this

end ForkPinningEntropyPort

theorem solution {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    {κ β : Type*} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]
    (X : Ω → κ) (Y : Ω → β) : mutualInfo X Y ≤ H Y := by
  unfold mutualInfo
  have := ForkPinningEntropyPort.entropy_le_entropy_joint X Y
  linarith
