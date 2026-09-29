-- Prove2me | solution 1 for MarkovEntanglement.meanFieldMap_isMeanFieldMap
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-30T23:27:07.349302+00:00
-- url     : https://prove2.me/submissions/c6c8bfeb-3bbc-4c0f-81af-12afe4322317

import Mathlib
import Definitions.Def_markov_entanglement_meanfield

open scoped BigOperators
open MarkovEntanglement

/-- Summing a function of an agent's local state over the agents equals summing over the
local states, weighted by how many agents sit in each. -/
theorem me_sum_fiber {S : Type*} [Fintype S] [DecidableEq S] {N : ℕ} (s : Fin N → S)
    (F : S → ℝ) : ∑ i : Fin N, F (s i) = ∑ x : S, (stateCount s x : ℝ) * F x := by
  rw [← Finset.sum_fiberwise_of_maps_to (t := (Finset.univ : Finset S)) (g := s)
      (fun i _ => Finset.mem_univ (s i)) (fun i => F (s i))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have h : ∀ i ∈ Finset.univ.filter (fun i => s i = x), F (s i) = F x := by
    intro i hi
    simp only [Finset.mem_filter] at hi
    rw [hi.2]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  rfl

/-- The number of agents in a state times the index policy's activation probability there is
the number of agents actually activated out of that state. -/
theorem me_count_mul_prob {S : Type*} [Fintype S] [DecidableEq S] {N : ℕ}
    (ν : S → ℝ) (M : ℕ) (s : Fin N → S) (x : S) :
    (stateCount s x : ℝ) * indexActivationProb ν M s x = (activateCount ν M s x : ℝ) := by
  unfold indexActivationProb activateCount
  split_ifs with h
  · rw [h]; simp
  · have hne : ((stateCount s x : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 h
    field_simp

/-- The higher-priority mass of a configuration is the higher-priority count over `N`. -/
theorem me_hpm_eq {S : Type*} [Fintype S] [DecidableEq S] {N : ℕ}
    (ν : S → ℝ) (s : Fin N → S) (x : S) :
    higherPriorityMass ν (configuration s) x = (higherPriorityCount ν s x : ℝ) / (N : ℝ) := by
  unfold higherPriorityMass higherPriorityCount configuration
  rw [Nat.cast_sum, Finset.sum_div]

/-- The continuum activated fraction at the exact activation fraction `M / N` of an `N`-agent
system is the activated count divided by `N`. -/
theorem me_activateFraction_eq {S : Type*} [Fintype S] [DecidableEq S] {N : ℕ}
    (ν : S → ℝ) (M : ℕ) (hN : 0 < N) (s : Fin N → S) (x : S) :
    activateFraction ν ((M : ℝ) / (N : ℝ)) (configuration s) x
      = (activateCount ν M s x : ℝ) / (N : ℝ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  unfold activateFraction
  rw [me_hpm_eq, div_sub_div_same]
  unfold configuration activateCount
  rcases le_total (higherPriorityCount ν s x) M with hle | hlt
  · have h1 : (0 : ℝ) ≤ ((M : ℝ) - (higherPriorityCount ν s x : ℝ)) / (N : ℝ) := by
      have : ((higherPriorityCount ν s x : ℝ)) ≤ (M : ℝ) := by exact_mod_cast hle
      positivity
    rw [max_eq_right h1, min_div_div_right hNpos.le]
    congr 1
    rw [Nat.cast_min, Nat.cast_sub hle]
  · have h0 : M - higherPriorityCount ν s x = 0 := Nat.sub_eq_zero_of_le hlt
    have h1 : ((M : ℝ) - (higherPriorityCount ν s x : ℝ)) / (N : ℝ) ≤ 0 := by
      have : (M : ℝ) ≤ (higherPriorityCount ν s x : ℝ) := by exact_mod_cast hlt
      apply div_nonpos_of_nonpos_of_nonneg <;> linarith
    rw [max_eq_left h1, h0]
    simp
    positivity

theorem solution {S : Type*} [Fintype S] [DecidableEq S]
    (P0 P1 : Matrix S S ℝ) (ν : S → ℝ) (N M : ℕ) (hN : 0 < N) :
    IsMeanFieldMap (N := N) P0 P1 ν M
      (meanFieldMap P0 P1 ν ((M : ℝ) / (N : ℝ))) := by
  intro s y
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  rw [me_sum_fiber s (fun x => (1 / (N : ℝ)) *
    ((1 - indexActivationProb ν M s x) * P0 x y + indexActivationProb ν M s x * P1 x y))]
  unfold meanFieldMap
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [me_activateFraction_eq ν M hN s x]
  have hc := me_count_mul_prob ν M s x
  show ((stateCount s x : ℝ) / (N : ℝ) - _) * _ + _ = _
  field_simp
  linear_combination (P0 x y - P1 x y) * hc
