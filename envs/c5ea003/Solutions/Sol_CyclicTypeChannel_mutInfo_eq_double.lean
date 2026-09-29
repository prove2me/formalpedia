-- Prove2me | solution 1 for CyclicTypeChannel.mutInfo_eq_double
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:26:36.481101+00:00
-- url     : https://prove2.me/submissions/79d92dc8-5804-4654-8647-1157b0023123

-- Sol generated from Shared/CyclicTypeChannelNonneg.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_condEnt_eq_joint
import Theorems.Thm_CyclicTypeChannel_sum_fiber_card
import Theorems.Thm_CyclicTypeChannel_sum_logb_fiber
/-
# Non-negativity of the counting mutual information

The channel quantities used for the cyclic splitting-type channel are honest
information-theoretic objects: this file proves the Gibbs inequality for the
counting framework, i.e. `I(g ; k) ≥ 0` for every pair of read-outs of a finite
uniform source, and derives the sandwich `0 ≤ I(g ; k) ≤ H(g)`.

The proof is the classical one: `I` is the Kullback–Leibler divergence between
the joint law and the product of the marginals, and `log t ≤ t - 1`.
-/

open CyclicTypeChannel

open Finset

variable {α β γ : Type*} [DecidableEq β] [DecidableEq γ]

/-! ## 1. The analytic core -/



/-! ## 2. The joint count array of two read-outs -/


variable (s : Finset α) (g : α → β) (k : α → γ)

lemma jointCount_sum_g (c : γ) :
    ∑ v ∈ s.image g, #{x ∈ s | k x = c ∧ g x = v} = #{x ∈ s | k x = c} := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := g) (t := s.image g) (fun x hx => mem_image_of_mem g (mem_filter.1 hx).1)]
  exact Finset.sum_congr rfl fun v _ => by simp only [Finset.filter_filter]

lemma jointCount_sum_k (v : β) :
    ∑ c ∈ s.image k, #{x ∈ s | k x = c ∧ g x = v} = #{x ∈ s | g x = v} := by
  classical
  rw [Finset.card_eq_sum_card_fiberwise
    (f := k) (t := s.image k) (fun x hx => mem_image_of_mem k (mem_filter.1 hx).1)]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Finset.filter_filter]
  exact congrArg _ (Finset.filter_congr fun x _ => by tauto)


/-- `uEnt` written as a sum over the image. -/
lemma uEnt_eq_image (s : Finset α) (g : α → β) :
    uEnt s g = Real.logb 2 s.card
      - (∑ v ∈ s.image g, (#{x ∈ s | g x = v} : ℝ) * Real.logb 2 (#{x ∈ s | g x = v} : ℝ))
        / s.card := by
  rw [uEnt, sum_logb_fiber]



/-! ## 3. Non-negativity -/





open CyclicTypeChannel in
lemma solution(s : Finset α) (g : α → β) (k : α → γ) (hs : s.Nonempty) :
    mutInfo s g k = ∑ c ∈ s.image k, ∑ v ∈ s.image g,
      ((#{x ∈ s | k x = c ∧ g x = v} : ℝ) / s.card) *
        (Real.logb 2 (s.card : ℝ) - Real.logb 2 (#{x ∈ s | g x = v} : ℝ)
          - Real.logb 2 (#{x ∈ s | k x = c} : ℝ)
          + Real.logb 2 (#{x ∈ s | k x = c ∧ g x = v} : ℝ)) := by
  classical
  have hN0 : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast card_pos.2 hs
  have hsum_M : ∑ c ∈ s.image k, (#{x ∈ s | k x = c} : ℝ) = (s.card : ℝ) := by
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) (sum_fiber_card s k)
  have hsum_nv : ∀ c ∈ s.image k,
      ∑ v ∈ s.image g, (#{x ∈ s | k x = c ∧ g x = v} : ℝ) = (#{x ∈ s | k x = c} : ℝ) := by
    intro c _
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) (jointCount_sum_g s g k c)
  have hsum_nc : ∀ v ∈ s.image g,
      ∑ c ∈ s.image k, (#{x ∈ s | k x = c ∧ g x = v} : ℝ) = (#{x ∈ s | g x = v} : ℝ) := by
    intro v _
    exact_mod_cast congrArg (Nat.cast (R := ℝ)) (jointCount_sum_k s g k v)
  have e1 : ∑ c ∈ s.image k, ∑ v ∈ s.image g,
      ((#{x ∈ s | k x = c ∧ g x = v} : ℝ) / s.card) * Real.logb 2 (s.card : ℝ)
      = Real.logb 2 (s.card : ℝ) := by
    have hstep : ∑ c ∈ s.image k, ∑ v ∈ s.image g,
        ((#{x ∈ s | k x = c ∧ g x = v} : ℝ) / s.card) * Real.logb 2 (s.card : ℝ)
        = ((∑ c ∈ s.image k, ∑ v ∈ s.image g, (#{x ∈ s | k x = c ∧ g x = v} : ℝ)) / s.card)
            * Real.logb 2 (s.card : ℝ) := by
      simp only [← Finset.sum_div, ← Finset.sum_mul]
    rw [hstep, Finset.sum_congr rfl hsum_nv, hsum_M, div_self (ne_of_gt hN0), one_mul]
  have e2 : ∑ c ∈ s.image k, ∑ v ∈ s.image g,
      ((#{x ∈ s | k x = c ∧ g x = v} : ℝ) / s.card) * Real.logb 2 (#{x ∈ s | g x = v} : ℝ)
      = (∑ v ∈ s.image g,
          (#{x ∈ s | g x = v} : ℝ) * Real.logb 2 (#{x ∈ s | g x = v} : ℝ)) / s.card := by
    rw [Finset.sum_comm, Finset.sum_div]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← Finset.sum_mul, ← Finset.sum_div, hsum_nc v hv, div_mul_eq_mul_div]
  have e3 : ∑ c ∈ s.image k, ∑ v ∈ s.image g,
      ((#{x ∈ s | k x = c ∧ g x = v} : ℝ) / s.card) * Real.logb 2 (#{x ∈ s | k x = c} : ℝ)
      = ∑ c ∈ s.image k,
          ((#{x ∈ s | k x = c} : ℝ) / s.card) * Real.logb 2 (#{x ∈ s | k x = c} : ℝ) := by
    refine Finset.sum_congr rfl fun c hc => ?_
    rw [← Finset.sum_mul, ← Finset.sum_div, hsum_nv c hc]
  have e4 : ∑ c ∈ s.image k, ∑ v ∈ s.image g,
      ((#{x ∈ s | k x = c ∧ g x = v} : ℝ) / s.card)
        * Real.logb 2 (#{x ∈ s | k x = c ∧ g x = v} : ℝ)
      = ∑ c ∈ s.image k, (∑ v ∈ s.image g, (#{x ∈ s | k x = c ∧ g x = v} : ℝ)
          * Real.logb 2 (#{x ∈ s | k x = c ∧ g x = v} : ℝ)) / s.card := by
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun v _ => by ring
  have expand : ∑ c ∈ s.image k, ∑ v ∈ s.image g,
      ((#{x ∈ s | k x = c ∧ g x = v} : ℝ) / s.card) *
        (Real.logb 2 (s.card : ℝ) - Real.logb 2 (#{x ∈ s | g x = v} : ℝ)
          - Real.logb 2 (#{x ∈ s | k x = c} : ℝ)
          + Real.logb 2 (#{x ∈ s | k x = c ∧ g x = v} : ℝ))
      = (∑ c ∈ s.image k, ∑ v ∈ s.image g,
            ((#{x ∈ s | k x = c ∧ g x = v} : ℝ) / s.card) * Real.logb 2 (s.card : ℝ))
        - (∑ c ∈ s.image k, ∑ v ∈ s.image g,
            ((#{x ∈ s | k x = c ∧ g x = v} : ℝ) / s.card)
              * Real.logb 2 (#{x ∈ s | g x = v} : ℝ))
        - (∑ c ∈ s.image k, ∑ v ∈ s.image g,
            ((#{x ∈ s | k x = c ∧ g x = v} : ℝ) / s.card)
              * Real.logb 2 (#{x ∈ s | k x = c} : ℝ))
        + (∑ c ∈ s.image k, ∑ v ∈ s.image g,
            ((#{x ∈ s | k x = c ∧ g x = v} : ℝ) / s.card)
              * Real.logb 2 (#{x ∈ s | k x = c ∧ g x = v} : ℝ)) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _ => by ring
  rw [expand, e1, e2, e3, e4, mutInfo, uEnt_eq_image, condEnt_eq_joint,
    Finset.sum_sub_distrib]
  ring
