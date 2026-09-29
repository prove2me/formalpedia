-- Prove2me | solution 1 for CyclicTypeChannel.condEnt_eq_joint
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:25:17.48666+00:00
-- url     : https://prove2.me/submissions/3401047a-091e-4c22-935e-0d93dad97852

-- Sol generated from Shared/CyclicTypeChannelNonneg.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_fiber_card_pos
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




/-- `uEnt` written as a sum over the image. -/
lemma uEnt_eq_image (s : Finset α) (g : α → β) :
    uEnt s g = Real.logb 2 s.card
      - (∑ v ∈ s.image g, (#{x ∈ s | g x = v} : ℝ) * Real.logb 2 (#{x ∈ s | g x = v} : ℝ))
        / s.card := by
  rw [uEnt, sum_logb_fiber]



/-! ## 3. Non-negativity -/





open CyclicTypeChannel in
lemma solution(s : Finset α) (g : α → β) (k : α → γ) :
    condEnt s g k = ∑ c ∈ s.image k,
      (((#{x ∈ s | k x = c} : ℝ) / s.card) * Real.logb 2 (#{x ∈ s | k x = c} : ℝ)
        - (∑ v ∈ s.image g, (#{x ∈ s | k x = c ∧ g x = v} : ℝ)
            * Real.logb 2 (#{x ∈ s | k x = c ∧ g x = v} : ℝ)) / s.card) := by
  classical
  refine Finset.sum_congr rfl fun c hc => ?_
  obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
  have hMc : (0 : ℝ) < (#{x ∈ s | k x = k a} : ℝ) := by
    exact_mod_cast fiber_card_pos ha
  have hfilter : ∀ v : β, {x ∈ {x ∈ s | k x = k a} | g x = v} = {x ∈ s | k x = k a ∧ g x = v} := by
    intro v
    simp only [Finset.filter_filter]
  have hsubset : ({x ∈ s | k x = k a}).image g ⊆ s.image g := by
    intro v hv
    obtain ⟨b, hb, rfl⟩ := mem_image.1 hv
    exact mem_image_of_mem g (mem_filter.1 hb).1
  have hzero : ∀ v ∈ s.image g, v ∉ ({x ∈ s | k x = k a}).image g →
      (#{x ∈ s | k x = k a ∧ g x = v} : ℝ)
        * Real.logb 2 (#{x ∈ s | k x = k a ∧ g x = v} : ℝ) = 0 := by
    intro v _ hv
    have hemp : {x ∈ {x ∈ s | k x = k a} | g x = v} = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx hgx
      exact hv (mem_image.2 ⟨x, hx, hgx⟩)
    rw [← hfilter v, hemp]
    simp
  have hsub : uEnt {x ∈ s | k x = k a} g
      = Real.logb 2 (#{x ∈ s | k x = k a} : ℝ)
        - (∑ v ∈ s.image g, (#{x ∈ s | k x = k a ∧ g x = v} : ℝ)
            * Real.logb 2 (#{x ∈ s | k x = k a ∧ g x = v} : ℝ))
          / (#{x ∈ s | k x = k a} : ℝ) := by
    rw [uEnt_eq_image]
    simp only [hfilter]
    rw [Finset.sum_subset hsubset hzero]
  rw [hsub]
  field_simp
