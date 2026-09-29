-- Prove2me | solution 1 for TropicalDequantization.dequant_eq_trop_iff_card_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:36:41.309972+00:00
-- url     : https://prove2.me/submissions/ca0c7080-3958-423a-bac1-9983fa1eaa12

-- Sol generated from Tropical/SocialChoice/Dequantization.lean
import Mathlib
import Definitions.Def_Tropical_SocialChoice_Dequantization
/-
# Maslov dequantization of tropical aggregators

A second bridge, this time between **tropical (min-plus) aggregation** and
**classical analysis**: the log-sum-exp ("softmin") family

`F_ε x = -ε · log ( Σ_{i ∈ S} exp (-(x i + δ i)/ε) )`

is a family of genuinely classical, positive, smooth aggregators, and it
converges to the tropical aggregator `x ↦ min_{i ∈ S} (x i + δ i)` as `ε ↓ 0`.

Main results.

* `logSumExp_sandwich` : the two-sided, fully explicit estimate
  `A - ε log |S| ≤ -ε log Σ exp(-a i/ε) ≤ A`, where `A = min_{i ∈ S} a i`.
* `tendsto_logSumExp` : the resulting convergence as `ε ↓ 0`.
* `dequant_sub_trop_abs_le` : the dequantized aggregators converge to the
  tropical aggregator *uniformly in the profile*, with rate `ε log |S|`.
* `dequant_eq_trop_iff_card_eq_one` : the dequantization is *exact* (there is no
  deformation at all) precisely when the tropical support is a singleton, i.e.
  precisely for dictatorships.  This is the "dequantization stability of
  decisive coalitions" phenomenon in sharp form.
-/

open TropicalDequantization

open Finset

variable {ι : Type*}








/-! ## Dequantized aggregators -/







open TropicalDequantization in
theorem solution{S : Finset ι} (hS : S.Nonempty) (δ : ι → ℝ) :
    (∀ ε : ℝ, 0 < ε → ∀ x : ι → ℝ, dequant ε S δ x = tropAgg S hS δ x) ↔ S.card = 1 := by
  constructor
  · intro hstab
    have hx := hstab 1 one_pos (fun i => -δ i)
    have hzero : ∀ i, (fun i => (fun i => -δ i) i + δ i) i = 0 := by intro i; ring
    have hsum : (∑ i ∈ S, Real.exp (-((fun i => -δ i) i + δ i) / 1)) = S.card := by
      simp [hzero]
    have htrop : tropAgg S hS δ (fun i => -δ i) = 0 := by
      simp only [tropAgg]
      have : (fun i => (-δ i) + δ i) = fun _ : ι => (0:ℝ) := by funext i; ring
      rw [this]
      simp
    rw [htrop] at hx
    simp only [dequant, logSumExp] at hx
    rw [hsum] at hx
    have hlog : Real.log (S.card : ℝ) = 0 := by
      have h1 : (-1 : ℝ) * Real.log (S.card : ℝ) = 0 := by simpa using hx
      linarith
    have hcard : (1 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hS
    have : (S.card : ℝ) = 1 := by
      by_contra hne
      have h1 : (1 : ℝ) < S.card := lt_of_le_of_ne hcard (Ne.symm hne)
      have := Real.log_pos h1
      linarith
    exact_mod_cast this
  · intro hcard ε hε x
    obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.1 hcard
    subst hi₀
    simp only [dequant, tropAgg, logSumExp, Finset.sum_singleton, Finset.inf'_singleton,
      Real.log_exp]
    field_simp
