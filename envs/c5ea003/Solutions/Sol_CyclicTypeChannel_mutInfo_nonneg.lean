-- Prove2me | solution 1 for CyclicTypeChannel.mutInfo_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T22:28:13.133399+00:00
-- url     : https://prove2.me/submissions/7c61ebc3-55ec-4fa9-a337-e806bed1a97b

-- Sol generated from Shared/CyclicTypeChannelNonneg.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Theorems.Thm_CyclicTypeChannel_fiber_card_pos
import Theorems.Thm_CyclicTypeChannel_gibbs_double
import Theorems.Thm_CyclicTypeChannel_mutInfo_eq_double
import Theorems.Thm_CyclicTypeChannel_sum_fiber_card
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






/-! ## 3. Non-negativity -/





open CyclicTypeChannel in
theorem solution(s : Finset α) (g : α → β) (k : α → γ) : 0 ≤ mutInfo s g k := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp [mutInfo, condEnt, uEnt]
  have hN0 : (0 : ℝ) < (s.card : ℝ) := by exact_mod_cast card_pos.2 hs
  rw [mutInfo_eq_double s g k hs]
  refine gibbs_double (s.image k) (s.image g) (s.card : ℝ) hN0
    (fun c v => (#{x ∈ s | k x = c ∧ g x = v} : ℝ))
    (fun v => (#{x ∈ s | g x = v} : ℝ)) (fun c => (#{x ∈ s | k x = c} : ℝ))
    (fun c v => by positivity) ?_ ?_ ?_ ?_ ?_
  · intro v hv
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hv
    show (0 : ℝ) < (#{x ∈ s | g x = g a} : ℝ)
    exact_mod_cast fiber_card_pos ha
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := mem_image.1 hc
    show (0 : ℝ) < (#{x ∈ s | k x = k a} : ℝ)
    exact_mod_cast fiber_card_pos ha
  · show ∑ v ∈ s.image g, ((#{x ∈ s | g x = v} : ℕ) : ℝ) = (s.card : ℝ)
    exact_mod_cast sum_fiber_card s g
  · show ∑ c ∈ s.image k, ((#{x ∈ s | k x = c} : ℕ) : ℝ) = (s.card : ℝ)
    exact_mod_cast sum_fiber_card s k
  · intro c _
    show ∑ v ∈ s.image g, ((#{x ∈ s | k x = c ∧ g x = v} : ℕ) : ℝ)
      = ((#{x ∈ s | k x = c} : ℕ) : ℝ)
    exact_mod_cast jointCount_sum_g s g k c
