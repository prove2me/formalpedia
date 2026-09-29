-- Prove2me | solution 1 for ForkPinning.mutualInfo_pos_of_not_indep
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-20T18:57:30.063981+00:00
-- url     : https://prove2.me/submissions/0d2d54b4-7558-4b7f-9fff-d38770185506

import Mathlib
import Definitions.Def_Probability_ForkPinningCore

set_option maxHeartbeats 2000000
set_option linter.all false

-- ==== upstream: Packages/Catalog/Probability/ForkPinningCore.lean ====
/-
# Fork pinning: a finite information-theoretic core

This file develops, from scratch, the small amount of finite information theory needed to
state and prove the **fork-pinning criterion**:

> a binary "fork" (a two-valued statistic of a Frobenius element) is congruence-pinned by a
> Dirichlet character exactly when it factors through the abelianization of the Galois group.

The probabilistic model is the uniform measure on a finite type `Ω` (which, in the arithmetic
application, is the Galois group of the splitting field; Chebotarev equidistribution turns
"a random prime" into "a uniformly random Frobenius element").

Main results:

* `ForkPinning.negMulLog_sum_le` / `negMulLog_sum_lt` : super-additivity of `x ↦ -x log x`
  on non-negative families, with the strict form.
* `ForkPinning.entropy_le_entropy_joint` : `H X ≤ H (X, Y)` (conditional entropy is non-negative).
* `ForkPinning.pinned_iff_determines` : `I(X;Y) = H Y ↔ X determines Y`  — the pinning criterion.
* `ForkPinning.mutualInfo_le_entropy` : `I(X;Y) ≤ H Y`.
* `ForkPinning.mutualInfo_nonneg` : `0 ≤ I(X;Y)` (Gibbs / sub-additivity of entropy).
* `ForkPinning.mutualInfo_eq_zero_of_indep` : independence ⇒ flat fork.
* `ForkPinning.mutualInfo_const_left` : a constant statistic carries no information
  (the "within-face fork is flat" mechanism).
-/

namespace ForkPinning

open Finset Real

variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
variable {κ β : Type*} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]

/-! ## Basic definitions: uniform measure, entropy, mutual information -/

-- [dropped: platform already declares fiber]
-- [dropped: platform already declares prb]
-- [dropped: platform already declares H]
-- [dropped: platform already declares joint]
-- [dropped: platform already declares mutualInfo]
-- [dropped: platform already declares Determines]
lemma card_pos : 0 < (Fintype.card Ω : ℝ) := by
  exact_mod_cast Fintype.card_pos

omit [Fintype κ] in
lemma prb_nonneg (X : Ω → κ) (k : κ) : 0 ≤ prb X k :=
  div_nonneg (Nat.cast_nonneg _) (le_of_lt card_pos)

lemma sum_prb (X : Ω → κ) : ∑ k : κ, prb X k = 1 := by
  have h : ∑ k : κ, ((fiber X k).card : ℝ) = (Fintype.card Ω : ℝ) := by
    have := Finset.card_eq_sum_card_fiberwise
      (f := X) (s := (univ : Finset Ω)) (t := (univ : Finset κ)) (by intro x _; exact mem_univ _)
    rw [Finset.card_univ] at this
    simp only [fiber]
    exact_mod_cast this.symm
  unfold prb
  rw [← Finset.sum_div, h, div_self (ne_of_gt card_pos)]

omit [Nonempty Ω] [Fintype κ] [Fintype β] in
lemma fiber_joint (X : Ω → κ) (Y : Ω → β) (k : κ) (b : β) :
    fiber (joint X Y) (k, b) = (fiber X k).filter (fun ω => Y ω = b) := by
  ext ω; simp [fiber, joint, Prod.ext_iff]

omit [Nonempty Ω] [Fintype κ] in
lemma sum_prb_joint (X : Ω → κ) (Y : Ω → β) (k : κ) :
    ∑ b : β, prb (joint X Y) (k, b) = prb X k := by
  simp only [prb, fiber_joint]
  rw [← Finset.sum_div]
  congr 1
  have := Finset.card_eq_sum_card_fiberwise
    (f := Y) (s := fiber X k) (t := (univ : Finset β)) (by intro x _; exact mem_univ _)
  exact_mod_cast this.symm

/-! ## Super-additivity of `negMulLog` -/

lemma negMulLog_sum_eq {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    negMulLog (∑ i ∈ s, f i) = ∑ i ∈ s, -(f i) * Real.log (∑ i ∈ s, f i) := by
  set S := ∑ i ∈ s, f i with hS
  simp only [neg_mul]
  rw [Finset.sum_neg_distrib, ← Finset.sum_mul, ← hS, negMulLog, neg_mul]

/-- Super-additivity: `-S log S ≤ ∑ -xᵢ log xᵢ` for a non-negative family with sum `S`. -/
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

/-- Strict super-additivity when one term is strictly between `0` and the total. -/
lemma negMulLog_sum_lt {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i ∈ s, 0 ≤ f i)
    {i₀ : ι} (hi₀ : i₀ ∈ s) (h0 : 0 < f i₀) (h1 : f i₀ < ∑ i ∈ s, f i) :
    negMulLog (∑ i ∈ s, f i) < ∑ i ∈ s, negMulLog (f i) := by
  set S := ∑ i ∈ s, f i with hS
  have key : ∀ i ∈ s, -(f i) * Real.log S ≤ negMulLog (f i) := by
    intro i hi
    rcases eq_or_lt_of_le (hf i hi) with h0' | h0'
    · simp [negMulLog, ← h0']
    · have hle : f i ≤ S := Finset.single_le_sum hf hi
      have : Real.log (f i) ≤ Real.log S := Real.log_le_log h0' hle
      unfold negMulLog
      nlinarith
  have keystrict : -(f i₀) * Real.log S < negMulLog (f i₀) := by
    have : Real.log (f i₀) < Real.log S := Real.log_lt_log h0 h1
    unfold negMulLog
    nlinarith
  calc negMulLog S = ∑ i ∈ s, -(f i) * Real.log S := by rw [hS, ← negMulLog_sum_eq]
    _ < ∑ i ∈ s, negMulLog (f i) := Finset.sum_lt_sum key ⟨i₀, hi₀, keystrict⟩

/-! ## Conditional entropy is non-negative -/

omit [Nonempty Ω] in
lemma entropy_joint_eq (X : Ω → κ) (Y : Ω → β) :
    H (joint X Y) = ∑ k : κ, ∑ b : β, negMulLog (prb (joint X Y) (k, b)) := by
  unfold H
  rw [Fintype.sum_prod_type]

/-- `H X ≤ H (X,Y)` : the conditional entropy `H(Y|X)` is non-negative. -/
theorem entropy_le_entropy_joint (X : Ω → κ) (Y : Ω → β) : H X ≤ H (joint X Y) := by
  rw [entropy_joint_eq]
  unfold H
  refine Finset.sum_le_sum ?_
  intro k _
  have := negMulLog_sum_le (univ : Finset β) (fun b => prb (joint X Y) (k, b))
    (fun b _ => prb_nonneg _ _)
  rwa [sum_prb_joint X Y k] at this

/-! ## The pinning criterion -/

omit [Nonempty Ω] in
lemma entropy_joint_eq_of_determines {X : Ω → κ} {Y : Ω → β} (h : Determines X Y) :
    H (joint X Y) = H X := by
  rw [entropy_joint_eq]
  unfold H
  refine Finset.sum_congr rfl ?_
  intro k _
  by_cases hk : (fiber X k).Nonempty
  · obtain ⟨ω₀, hω₀⟩ := hk
    have hXω₀ : X ω₀ = k := by simpa [fiber] using hω₀
    have hfib : ∀ ω ∈ fiber X k, Y ω = Y ω₀ := by
      intro ω hω
      have hXω : X ω = k := by simpa [fiber] using hω
      exact h ω ω₀ (by rw [hXω, hXω₀])
    have hmain : prb (joint X Y) (k, Y ω₀) = prb X k := by
      have hfilter : (fiber X k).filter (fun ω => Y ω = Y ω₀) = fiber X k :=
        Finset.filter_true_of_mem (fun ω hω => hfib ω hω)
      rw [prb, fiber_joint, hfilter, prb]
    have hother : ∀ b : β, b ≠ Y ω₀ → prb (joint X Y) (k, b) = 0 := by
      intro b hb
      have hfilter : (fiber X k).filter (fun ω => Y ω = b) = ∅ := by
        apply Finset.filter_false_of_mem
        intro ω hω hYω
        exact hb (by rw [← hYω, hfib ω hω])
      rw [prb, fiber_joint, hfilter]
      simp
    rw [Finset.sum_eq_single (Y ω₀)]
    · rw [hmain]
    · intro b _ hb
      rw [hother b hb, negMulLog_zero]
    · intro hcontra
      exact absurd (mem_univ (Y ω₀)) hcontra
  · have hempty : fiber X k = ∅ := Finset.not_nonempty_iff_eq_empty.mp hk
    have hpk : prb X k = 0 := by unfold prb; rw [hempty]; simp
    have hall : ∀ b : β, prb (joint X Y) (k, b) = 0 := by
      intro b
      rw [prb, fiber_joint, hempty]
      simp
    simp [hall, hpk]

lemma determines_of_entropy_joint_eq {X : Ω → κ} {Y : Ω → β} (h : H (joint X Y) = H X) :
    Determines X Y := by
  by_contra hcon
  unfold Determines at hcon
  push_neg at hcon
  obtain ⟨ω, ω', hX, hY⟩ := hcon
  set k := X ω with hk
  have hmem : ω ∈ (fiber X k).filter (fun x => Y x = Y ω) := by simp [fiber, hk]
  have hmem' : ω' ∈ (fiber X k).filter (fun x => Y x = Y ω') := by simp [fiber, hk, hX.symm]
  have hpos : 0 < prb (joint X Y) (k, Y ω) := by
    rw [prb, fiber_joint]
    apply div_pos _ card_pos
    have : 0 < ((fiber X k).filter (fun x => Y x = Y ω)).card :=
      Finset.card_pos.mpr ⟨ω, hmem⟩
    exact_mod_cast this
  have hpos' : 0 < prb (joint X Y) (k, Y ω') := by
    rw [prb, fiber_joint]
    apply div_pos _ card_pos
    have : 0 < ((fiber X k).filter (fun x => Y x = Y ω')).card :=
      Finset.card_pos.mpr ⟨ω', hmem'⟩
    exact_mod_cast this
  have hsumlt : prb (joint X Y) (k, Y ω) < ∑ b : β, prb (joint X Y) (k, b) := by
    have h2 : ∑ b ∈ ({Y ω, Y ω'} : Finset β), prb (joint X Y) (k, b)
        ≤ ∑ b : β, prb (joint X Y) (k, b) :=
      Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun b _ _ => prb_nonneg _ _)
    rw [Finset.sum_pair hY] at h2
    linarith
  have hstrict : negMulLog (prb X k) < ∑ b : β, negMulLog (prb (joint X Y) (k, b)) := by
    have hlt : prb (joint X Y) (k, Y ω) < ∑ b : β, prb (joint X Y) (k, b) := hsumlt
    have := negMulLog_sum_lt (univ : Finset β) (fun b => prb (joint X Y) (k, b))
      (fun b _ => prb_nonneg _ _) (mem_univ (Y ω)) hpos hlt
    rwa [sum_prb_joint X Y k] at this
  have hle : ∀ k' : κ, negMulLog (prb X k') ≤ ∑ b : β, negMulLog (prb (joint X Y) (k', b)) := by
    intro k'
    have := negMulLog_sum_le (univ : Finset β) (fun b => prb (joint X Y) (k', b))
      (fun b _ => prb_nonneg _ _)
    rwa [sum_prb_joint X Y k'] at this
  have hlt : H X < H (joint X Y) := by
    rw [entropy_joint_eq]
    unfold H
    exact Finset.sum_lt_sum (fun k' _ => hle k') ⟨k, mem_univ k, hstrict⟩
  rw [h] at hlt
  exact lt_irrefl _ hlt

/-- **Fork-pinning criterion (information-theoretic form).**
A fork `Y` gives up all of its entropy to the statistic `X` exactly when `X` determines `Y`. -/
theorem pinned_iff_determines (X : Ω → κ) (Y : Ω → β) :
    mutualInfo X Y = H Y ↔ Determines X Y := by
  unfold mutualInfo
  constructor
  · intro h
    exact determines_of_entropy_joint_eq (by linarith)
  · intro h
    rw [entropy_joint_eq_of_determines h]; ring

/-- Mutual information never exceeds the entropy of the fork. -/
theorem mutualInfo_le_entropy (X : Ω → κ) (Y : Ω → β) : mutualInfo X Y ≤ H Y := by
  unfold mutualInfo
  have := entropy_le_entropy_joint X Y
  linarith

/-- If `X` does **not** determine `Y`, the pinning is strictly partial. -/
theorem mutualInfo_lt_entropy_of_not_determines (X : Ω → κ) (Y : Ω → β)
    (h : ¬ Determines X Y) : mutualInfo X Y < H Y := by
  rcases lt_or_eq_of_le (mutualInfo_le_entropy X Y) with h' | h'
  · exact h'
  · exact absurd ((pinned_iff_determines X Y).mp h') h

omit [Nonempty Ω] [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β] in
/-- Factoring through `X` is the same as being determined by `X`. -/
theorem determines_iff_factors [Inhabited β] (X : Ω → κ) (Y : Ω → β) :
    Determines X Y ↔ ∃ ψ : κ → β, Y = ψ ∘ X := by
  classical
  constructor
  · intro h
    refine ⟨fun k => if hk : ∃ ω, X ω = k then Y hk.choose else default, ?_⟩
    funext ω
    have hk : ∃ ω', X ω' = X ω := ⟨ω, rfl⟩
    simp only [Function.comp_apply, dif_pos hk]
    exact (h hk.choose ω hk.choose_spec).symm
  · rintro ⟨ψ, rfl⟩ ω ω' hω
    simp [Function.comp_apply, hω]

/-! ## Flatness -/

omit [Nonempty Ω] [Fintype κ] in
lemma fiber_const_self (c : κ) : fiber (fun _ : Ω => c) c = univ := by
  ext ω; simp [fiber]

omit [Nonempty Ω] [Fintype κ] in
lemma fiber_const_ne {c k : κ} (h : k ≠ c) : fiber (fun _ : Ω => c) k = ∅ := by
  ext ω; simp [fiber, Ne.symm h]

/-- A constant statistic carries no information: within-face forks are flat. -/
theorem mutualInfo_const_left (c : κ) (Y : Ω → β) :
    mutualInfo (fun _ => c) Y = 0 := by
  have hX : H (fun _ : Ω => c) = 0 := by
    unfold H
    rw [Finset.sum_eq_single c]
    · rw [prb, fiber_const_self, Finset.card_univ,
        div_self (ne_of_gt (card_pos (Ω := Ω))), negMulLog_one]
    · intro b _ hb
      rw [prb, fiber_const_ne hb]
      simp
    · intro hc; exact absurd (mem_univ c) hc
  have hjoint : H (joint (fun _ : Ω => c) Y) = H Y := by
    rw [entropy_joint_eq]
    unfold H
    rw [Finset.sum_eq_single c]
    · refine Finset.sum_congr rfl (fun b _ => ?_)
      congr 1
      rw [prb, fiber_joint, fiber_const_self, prb, fiber]
    · intro k _ hk
      refine Finset.sum_eq_zero (fun b _ => ?_)
      have hz : prb (joint (fun _ : Ω => c) Y) (k, b) = 0 := by
        rw [prb, fiber_joint, fiber_const_ne hk]
        simp
      rw [hz, negMulLog_zero]
    · intro hc; exact absurd (mem_univ c) hc
  unfold mutualInfo
  rw [hX, hjoint]; ring

/-- Under independence the joint entropy is additive. -/
theorem entropy_joint_of_indep (X : Ω → κ) (Y : Ω → β)
    (h : ∀ k b, prb (joint X Y) (k, b) = prb X k * prb Y b) :
    H (joint X Y) = H X + H Y := by
  rw [entropy_joint_eq]
  have hterm : ∀ k b, negMulLog (prb (joint X Y) (k, b))
      = prb Y b * negMulLog (prb X k) + prb X k * negMulLog (prb Y b) := by
    intro k b; rw [h k b, negMulLog_mul]
  calc ∑ k : κ, ∑ b : β, negMulLog (prb (joint X Y) (k, b))
      = ∑ k : κ, ∑ b : β, (prb Y b * negMulLog (prb X k) + prb X k * negMulLog (prb Y b)) :=
        Finset.sum_congr rfl (fun k _ => Finset.sum_congr rfl (fun b _ => hterm k b))
    _ = ∑ k : κ, (negMulLog (prb X k) * (∑ b : β, prb Y b)
          + prb X k * (∑ b : β, negMulLog (prb Y b))) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
        ring
    _ = H X + H Y := by
        rw [sum_prb Y, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, sum_prb X]
        unfold H
        ring

/-- Independence ⇒ zero mutual information (a *flat* fork). -/
theorem mutualInfo_eq_zero_of_indep (X : Ω → κ) (Y : Ω → β)
    (h : ∀ k b, prb (joint X Y) (k, b) = prb X k * prb Y b) : mutualInfo X Y = 0 := by
  unfold mutualInfo
  rw [entropy_joint_of_indep X Y h]; ring

omit [Nonempty Ω] in
/-- Entropy is invariant under relabelling the value type by a bijection. -/
theorem entropy_congr_equiv {κ' : Type*} [Fintype κ'] [DecidableEq κ'] (e : κ ≃ κ')
    (X : Ω → κ) : H (fun ω => e (X ω)) = H X := by
  unfold H
  rw [← Equiv.sum_comp e (fun k' => negMulLog (prb (fun ω => e (X ω)) k'))]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  have hset : fiber (fun ω => e (X ω)) (e k) = fiber X k := by
    ext ω; simp [fiber, e.injective.eq_iff]
  rw [prb, hset, prb]

/-! ## Non-negativity of mutual information (Gibbs), with the equality case -/

omit [Fintype κ] in
lemma prb_joint_le_left (X : Ω → κ) (Y : Ω → β) (k : κ) (b : β) :
    prb (joint X Y) (k, b) ≤ prb X k := by
  have hle : prb (joint X Y) (k, b) ≤ ∑ b' : β, prb (joint X Y) (k, b') :=
    Finset.single_le_sum (f := fun b' => prb (joint X Y) (k, b'))
      (fun b' _ => prb_nonneg _ _) (mem_univ b)
  rwa [sum_prb_joint X Y k] at hle

omit [Nonempty Ω] [Fintype κ] [Fintype β] in
lemma prb_joint_swap (X : Ω → κ) (Y : Ω → β) (k : κ) (b : β) :
    prb (joint Y X) (b, k) = prb (joint X Y) (k, b) := by
  have hset : fiber (joint Y X) (b, k) = fiber (joint X Y) (k, b) := by
    ext ω; simp [fiber, joint, Prod.ext_iff, and_comm]
  rw [prb, prb, hset]

omit [Fintype β] in
lemma prb_joint_le_right (X : Ω → κ) (Y : Ω → β) (k : κ) (b : β) :
    prb (joint X Y) (k, b) ≤ prb Y b := by
  rw [← prb_joint_swap X Y k b]
  exact prb_joint_le_left Y X b k

omit [Nonempty Ω] in
/-- The Kullback–Leibler form of the mutual information. -/
lemma mutualInfo_eq_sum_kl (X : Ω → κ) (Y : Ω → β) :
    mutualInfo X Y = ∑ k : κ, ∑ b : β,
      (prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))
        - prb (joint X Y) (k, b) * Real.log (prb X k)
        - prb (joint X Y) (k, b) * Real.log (prb Y b)) := by
  set r : κ × β → ℝ := fun kb => prb (joint X Y) kb with hr
  have hrp : ∀ k, ∑ b : β, r (k, b) = prb X k := fun k => sum_prb_joint X Y k
  have hrq : ∀ b, ∑ k : κ, r (k, b) = prb Y b := by
    intro b
    calc ∑ k : κ, r (k, b) = ∑ k : κ, prb (joint Y X) (b, k) :=
          Finset.sum_congr rfl (fun k _ => (prb_joint_swap X Y k b).symm)
      _ = prb Y b := sum_prb_joint Y X b
  have hHX : H X = ∑ k : κ, ∑ b : β, (- r (k, b) * Real.log (prb X k)) := by
    unfold H
    refine Finset.sum_congr rfl (fun k _ => ?_)
    have hk : ∑ b : β, (- r (k, b) * Real.log (prb X k)) = negMulLog (prb X k) := by
      simp only [neg_mul]
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hrp k, negMulLog, neg_mul]
    rw [hk]
  have hHY : H Y = ∑ k : κ, ∑ b : β, (- r (k, b) * Real.log (prb Y b)) := by
    have hHY' : H Y = ∑ b : β, ∑ k : κ, (- r (k, b) * Real.log (prb Y b)) := by
      unfold H
      refine Finset.sum_congr rfl (fun b _ => ?_)
      have hb : ∑ k : κ, (- r (k, b) * Real.log (prb Y b)) = negMulLog (prb Y b) := by
        simp only [neg_mul]
        rw [Finset.sum_neg_distrib, ← Finset.sum_mul, hrq b, negMulLog, neg_mul]
      rw [hb]
    rw [hHY', Finset.sum_comm]
  have hHJ : H (joint X Y) = ∑ k : κ, ∑ b : β, negMulLog (r (k, b)) := entropy_joint_eq X Y
  unfold mutualInfo
  rw [hHX, hHY, hHJ, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  unfold negMulLog
  ring

/-- One Gibbs term: `r log (r / (p q)) ≥ r − p q`, written additively. -/
lemma gibbs_term_le {r p q : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hrp : r ≤ p) (hrq : r ≤ q) :
    -(r * Real.log r - r * Real.log p - r * Real.log q) ≤ p * q - r := by
  rcases eq_or_lt_of_le hr with h0 | h0
  · have hpq : 0 ≤ p * q := mul_nonneg hp hq
    rw [← h0]; simpa using hpq
  · have hpk : 0 < p := lt_of_lt_of_le h0 hrp
    have hqb : 0 < q := lt_of_lt_of_le h0 hrq
    have hlog : Real.log (p * q / r) ≤ p * q / r - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hsplit : Real.log (p * q / r) = Real.log p + Real.log q - Real.log r := by
      rw [Real.log_div (by positivity) (ne_of_gt h0), Real.log_mul (ne_of_gt hpk) (ne_of_gt hqb)]
    rw [hsplit] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt h0)
    have hfield : r * (p * q / r - 1) = p * q - r := by field_simp
    nlinarith [hmul, hfield]

/-- The strict Gibbs term: strict unless `r = p q`. -/
lemma gibbs_term_lt {r p q : ℝ} (hr : 0 ≤ r) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hrp : r ≤ p) (hrq : r ≤ q) (hne : r ≠ p * q) :
    -(r * Real.log r - r * Real.log p - r * Real.log q) < p * q - r := by
  rcases eq_or_lt_of_le hr with h0 | h0
  · have hpq : 0 ≤ p * q := mul_nonneg hp hq
    have hpq' : p * q ≠ 0 := by rw [← h0] at hne; exact fun hzero => hne hzero.symm
    have : 0 < p * q := lt_of_le_of_ne hpq (Ne.symm hpq')
    rw [← h0]; simpa using this
  · have hpk : 0 < p := lt_of_lt_of_le h0 hrp
    have hqb : 0 < q := lt_of_lt_of_le h0 hrq
    have hx1 : p * q / r ≠ 1 := by
      intro hx
      apply hne
      field_simp at hx
      linarith [hx]
    have hlog : Real.log (p * q / r) < p * q / r - 1 :=
      Real.log_lt_sub_one_of_pos (by positivity) hx1
    have hsplit : Real.log (p * q / r) = Real.log p + Real.log q - Real.log r := by
      rw [Real.log_div (by positivity) (ne_of_gt h0), Real.log_mul (ne_of_gt hpk) (ne_of_gt hqb)]
    rw [hsplit] at hlog
    have hmul := mul_lt_mul_of_pos_left hlog h0
    have hfield : r * (p * q / r - 1) = p * q - r := by field_simp
    nlinarith [hmul, hfield]

lemma sum_prod_prb_sub_joint (X : Ω → κ) (Y : Ω → β) :
    ∑ k : κ, ∑ b : β, (prb X k * prb Y b - prb (joint X Y) (k, b)) = 0 := by
  have hk0 : ∀ k : κ, ∑ b : β, (prb X k * prb Y b - prb (joint X Y) (k, b)) = 0 := by
    intro k
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, sum_prb Y, sum_prb_joint X Y k]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hk0 k)]
  simp

theorem mutualInfo_nonneg (X : Ω → κ) (Y : Ω → β) : 0 ≤ mutualInfo X Y := by
  have hsum : ∑ k : κ, ∑ b : β,
      (-(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))
        - prb (joint X Y) (k, b) * Real.log (prb X k)
        - prb (joint X Y) (k, b) * Real.log (prb Y b)))
      ≤ ∑ k : κ, ∑ b : β, (prb X k * prb Y b - prb (joint X Y) (k, b)) :=
    Finset.sum_le_sum (fun k _ => Finset.sum_le_sum (fun b _ =>
      gibbs_term_le (prb_nonneg _ _) (prb_nonneg _ _) (prb_nonneg _ _)
        (prb_joint_le_left X Y k b) (prb_joint_le_right X Y k b)))
  rw [sum_prod_prb_sub_joint X Y] at hsum
  have hneg : ∑ k : κ, ∑ b : β,
      (-(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))
        - prb (joint X Y) (k, b) * Real.log (prb X k)
        - prb (joint X Y) (k, b) * Real.log (prb Y b)))
      = - mutualInfo X Y := by
    rw [mutualInfo_eq_sum_kl]
    simp only [Finset.sum_neg_distrib]
  rw [hneg] at hsum
  linarith

/-- **Strict positivity off independence.** -/
theorem mutualInfo_pos_of_not_indep (X : Ω → κ) (Y : Ω → β)
    (h : ¬ (∀ k b, prb (joint X Y) (k, b) = prb X k * prb Y b)) : 0 < mutualInfo X Y := by
  push_neg at h
  obtain ⟨k₀, b₀, hne⟩ := h
  have hstrict : ∑ k : κ, ∑ b : β,
      (-(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))
        - prb (joint X Y) (k, b) * Real.log (prb X k)
        - prb (joint X Y) (k, b) * Real.log (prb Y b)))
      < ∑ k : κ, ∑ b : β, (prb X k * prb Y b - prb (joint X Y) (k, b)) := by
    refine Finset.sum_lt_sum (fun k _ => Finset.sum_le_sum (fun b _ =>
      gibbs_term_le (prb_nonneg _ _) (prb_nonneg _ _) (prb_nonneg _ _)
        (prb_joint_le_left X Y k b) (prb_joint_le_right X Y k b))) ⟨k₀, mem_univ k₀, ?_⟩
    refine Finset.sum_lt_sum (fun b _ =>
      gibbs_term_le (prb_nonneg _ _) (prb_nonneg _ _) (prb_nonneg _ _)
        (prb_joint_le_left X Y k₀ b) (prb_joint_le_right X Y k₀ b)) ⟨b₀, mem_univ b₀, ?_⟩
    exact gibbs_term_lt (prb_nonneg _ _) (prb_nonneg _ _) (prb_nonneg _ _)
      (prb_joint_le_left X Y k₀ b₀) (prb_joint_le_right X Y k₀ b₀) hne
  rw [sum_prod_prb_sub_joint X Y] at hstrict
  have hneg : ∑ k : κ, ∑ b : β,
      (-(prb (joint X Y) (k, b) * Real.log (prb (joint X Y) (k, b))
        - prb (joint X Y) (k, b) * Real.log (prb X k)
        - prb (joint X Y) (k, b) * Real.log (prb Y b)))
      = - mutualInfo X Y := by
    rw [mutualInfo_eq_sum_kl]
    simp only [Finset.sum_neg_distrib]
  rw [hneg] at hstrict
  linarith

/-- **Flatness is exactly independence.**  A fork is flat for a statistic iff the two are
independent. -/
theorem mutualInfo_eq_zero_iff_indep (X : Ω → κ) (Y : Ω → β) :
    mutualInfo X Y = 0 ↔ ∀ k b, prb (joint X Y) (k, b) = prb X k * prb Y b := by
  constructor
  · intro h
    by_contra hcon
    exact absurd h (ne_of_gt (mutualInfo_pos_of_not_indep X Y hcon))
  · exact mutualInfo_eq_zero_of_indep X Y

/-! ## Capacity: the fork can learn at most `log |κ|` -/

/-- Maximum-entropy bound. -/
theorem entropy_le_log_card (X : Ω → κ) : H X ≤ Real.log (Fintype.card κ) := by
  have hne : Nonempty κ := ⟨X (Classical.arbitrary Ω)⟩
  have hn : (0 : ℝ) < Fintype.card κ := by exact_mod_cast Fintype.card_pos
  have hterm : ∀ k : κ,
      negMulLog (prb X k) - prb X k * Real.log (Fintype.card κ)
        ≤ 1 / (Fintype.card κ) - prb X k := by
    intro k
    rcases eq_or_lt_of_le (prb_nonneg X k) with h0 | h0
    · rw [← h0]
      simp only [negMulLog_zero, zero_mul, sub_zero, sub_self]
      positivity
    · have hlog : Real.log (1 / (prb X k * Fintype.card κ))
          ≤ 1 / (prb X k * Fintype.card κ) - 1 :=
        Real.log_le_sub_one_of_pos (by positivity)
      have hid : negMulLog (prb X k) - prb X k * Real.log (Fintype.card κ)
          = prb X k * Real.log (1 / (prb X k * Fintype.card κ)) := by
        rw [Real.log_div one_ne_zero (by positivity),
          Real.log_mul (ne_of_gt h0) (ne_of_gt hn), Real.log_one, negMulLog]
        ring
      rw [hid]
      have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt h0)
      have hfield : prb X k * (1 / (prb X k * Fintype.card κ) - 1)
          = 1 / (Fintype.card κ) - prb X k := by
        field_simp
      nlinarith [hmul, hfield]
  have hsum := Finset.sum_le_sum (fun k (_ : k ∈ (univ : Finset κ)) => hterm k)
  have hlhs : ∑ k : κ, (negMulLog (prb X k) - prb X k * Real.log (Fintype.card κ))
      = H X - Real.log (Fintype.card κ) := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, sum_prb X]
    unfold H
    ring
  have hrhs : ∑ _k : κ, (1 / (Fintype.card κ : ℝ) - prb X _k) = 0 := by
    rw [Finset.sum_sub_distrib, sum_prb X, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    norm_num
  rw [hlhs, hrhs] at hsum
  linarith

/-- **Capacity bound.**  Whatever the fork, its congruence content is capped by the entropy of
the observable: in the Galois setting, by `log |G^ab|`. -/
theorem mutualInfo_le_log_card (X : Ω → κ) (Y : Ω → β) :
    mutualInfo X Y ≤ Real.log (Fintype.card κ) := by
  have h1 : mutualInfo X Y ≤ H X := by
    have h2 : mutualInfo Y X ≤ H X := mutualInfo_le_entropy Y X
    have hswap : mutualInfo X Y = mutualInfo Y X := by
      unfold mutualInfo
      have hj : H (joint X Y) = H (joint Y X) := by
        have := entropy_congr_equiv (Ω := Ω) (Equiv.prodComm β κ) (joint Y X)
        rw [show (fun ω => (Equiv.prodComm β κ) (joint Y X ω)) = joint X Y from rfl] at this
        rw [this]
      rw [hj]; ring
    rw [hswap]; exact h2
  exact le_trans h1 (entropy_le_log_card X)

/-! ## Conditional entropy: the quantitative pinned fraction -/

/-- The conditional law of the fork given `X = k` (the value is irrelevant when `prb X k = 0`). -/
-- [dropped: platform already declares condPrb]
-- [dropped: platform already declares condEntropyAt]
-- [dropped: platform already declares condEntropy]
theorem condEntropy_eq_sum (X : Ω → κ) (Y : Ω → β) :
    condEntropy X Y = ∑ k : κ, prb X k * condEntropyAt X Y k := by
  unfold condEntropy condEntropyAt
  rw [entropy_joint_eq]
  unfold H
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rcases eq_or_lt_of_le (prb_nonneg X k) with h0 | h0
  · -- an empty fibre contributes nothing on either side
    have hall : ∀ b : β, prb (joint X Y) (k, b) = 0 := by
      intro b
      have hle := prb_joint_le_left X Y k b
      have hge := prb_nonneg (joint X Y) (k, b)
      rw [← h0] at hle
      linarith
    simp [hall, ← h0]
  · have hterm : ∀ b : β,
        negMulLog (condPrb X Y k b)
          = (negMulLog (prb (joint X Y) (k, b))
              + prb (joint X Y) (k, b) * Real.log (prb X k)) / prb X k := by
      intro b
      rcases eq_or_lt_of_le (prb_nonneg (joint X Y) (k, b)) with hr | hr
      · rw [condPrb, ← hr]
        simp
      · rw [condPrb, negMulLog, Real.log_div (ne_of_gt hr) (ne_of_gt h0), negMulLog]
        field_simp
        ring
    rw [Finset.sum_congr rfl (fun b _ => hterm b), ← Finset.sum_div, Finset.sum_add_distrib,
      ← Finset.sum_mul, sum_prb_joint X Y k]
    have hp : prb X k ≠ 0 := ne_of_gt h0
    rw [negMulLog, mul_div_cancel₀ _ hp]
    ring

/-- **The pinned fraction.**  The information a statistic carries about a fork is the fork's
entropy minus the average entropy left inside the fibres. -/
theorem mutualInfo_eq_entropy_sub_condEntropy (X : Ω → κ) (Y : Ω → β) :
    mutualInfo X Y = H Y - ∑ k : κ, prb X k * condEntropyAt X Y k := by
  rw [← condEntropy_eq_sum]
  unfold mutualInfo condEntropy
  ring

end ForkPinning
section
open ForkPinning
open Finset Real
variable {Ω : Type*} [Fintype Ω] [Nonempty Ω]
variable {κ β : Type*} [Fintype κ] [DecidableEq κ] [Fintype β] [DecidableEq β]

theorem solution (X : Ω → κ) (Y : Ω → β)
    (h : ¬ (∀ k b, prb (joint X Y) (k, b) = prb X k * prb Y b)) :
    0 < mutualInfo X Y := by
  first
  | exact ForkPinning.mutualInfo_pos_of_not_indep X Y h
  | exact ForkPinning.mutualInfo_pos_of_not_indep
  | exact @ForkPinning.mutualInfo_pos_of_not_indep X Y h
  | apply ForkPinning.mutualInfo_pos_of_not_indep
  | exact ForkPinning.mutualInfo_pos_of_not_indep ..


end
