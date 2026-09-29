-- Prove2me | solution 1 for TropicalDequantization.logSumExp_sandwich
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T09:38:50.71774+00:00
-- url     : https://prove2.me/submissions/83a987bd-040b-4414-a809-66bfdc0a9bf1

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


lemma sum_exp_pos {S : Finset ι} (hS : S.Nonempty) (ε : ℝ) (a : ι → ℝ) :
    0 < ∑ i ∈ S, Real.exp (-(a i) / ε) :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) hS

/-- Lower bound for the smoothed sum: it dominates the term at a minimizer. -/
lemma exp_le_sum_exp {S : Finset ι} (hS : S.Nonempty) (ε : ℝ) (a : ι → ℝ) :
    Real.exp (-(S.inf' hS a) / ε) ≤ ∑ i ∈ S, Real.exp (-(a i) / ε) := by
  obtain ⟨i₀, hi₀S, hi₀⟩ := Finset.exists_mem_eq_inf' hS a
  calc Real.exp (-(S.inf' hS a) / ε) = Real.exp (-(a i₀) / ε) := by rw [hi₀]
    _ ≤ ∑ i ∈ S, Real.exp (-(a i) / ε) :=
        Finset.single_le_sum (f := fun i => Real.exp (-(a i) / ε))
          (fun i _ => (Real.exp_pos _).le) hi₀S

/-- Upper bound for the smoothed sum. -/
lemma sum_exp_le {S : Finset ι} (hS : S.Nonempty) {ε : ℝ} (hε : 0 < ε) (a : ι → ℝ) :
    (∑ i ∈ S, Real.exp (-(a i) / ε)) ≤ S.card * Real.exp (-(S.inf' hS a) / ε) := by
  have hterm : ∀ i ∈ S, Real.exp (-(a i) / ε) ≤ Real.exp (-(S.inf' hS a) / ε) := by
    intro i hi
    have hle : S.inf' hS a ≤ a i := Finset.inf'_le a hi
    exact Real.exp_le_exp.2 (by gcongr)
  calc (∑ i ∈ S, Real.exp (-(a i) / ε)) ≤ ∑ _i ∈ S, Real.exp (-(S.inf' hS a) / ε) :=
        Finset.sum_le_sum hterm
    _ = S.card * Real.exp (-(S.inf' hS a) / ε) := by
        rw [Finset.sum_const, nsmul_eq_mul]




/-! ## Dequantized aggregators -/







open TropicalDequantization in
theorem solution{S : Finset ι} (hS : S.Nonempty) {ε : ℝ} (hε : 0 < ε) (a : ι → ℝ) :
    S.inf' hS a - ε * Real.log S.card ≤ logSumExp ε S a ∧ logSumExp ε S a ≤ S.inf' hS a := by
  set A := S.inf' hS a with hA
  set T := ∑ i ∈ S, Real.exp (-(a i) / ε) with hT
  have hpos : 0 < T := sum_exp_pos hS ε a
  have hlow : Real.exp (-A / ε) ≤ T := exp_le_sum_exp hS ε a
  have hhigh : T ≤ S.card * Real.exp (-A / ε) := sum_exp_le hS hε a
  have hcard : (0 : ℝ) < S.card := by
    exact_mod_cast Finset.card_pos.2 hS
  have hlog1 : -A / ε ≤ Real.log T := by
    have := Real.log_le_log (Real.exp_pos _) hlow
    rwa [Real.log_exp] at this
  have hlog2 : Real.log T ≤ Real.log S.card + (-A / ε) := by
    have h1 := Real.log_le_log hpos hhigh
    rwa [Real.log_mul (ne_of_gt hcard) (ne_of_gt (Real.exp_pos _)), Real.log_exp] at h1
  constructor
  · have hmul : -ε * Real.log T ≥ -ε * (Real.log S.card + (-A / ε)) :=
      mul_le_mul_of_nonpos_left hlog2 (by linarith)
    have hexp : -ε * (Real.log S.card + (-A / ε)) = A - ε * Real.log S.card := by
      field_simp; ring
    simp only [logSumExp, ← hT]
    linarith [hexp ▸ hmul]
  · have hmul : -ε * Real.log T ≤ -ε * (-A / ε) :=
      mul_le_mul_of_nonpos_left hlog1 (by linarith)
    have hexp : -ε * (-A / ε) = A := by field_simp
    simp only [logSumExp, ← hT]
    linarith [hexp ▸ hmul]
