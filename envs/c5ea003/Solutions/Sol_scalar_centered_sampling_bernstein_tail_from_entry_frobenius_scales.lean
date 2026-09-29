-- Prove2me | solution 1 for scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-21T20:29:24.419758+00:00
-- url     : https://prove2.me/submissions/d4bb7a67-adc4-40fa-9363-edd1c488b690

import Theorems.Thm_scalar_centered_sampling_qmoment_bernstein_estimate
import Theorems.Thm_scalar_centered_sampling_markov_tail_from_qmoment_bound

open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

namespace Prove3cbb

variable {n₁ n₂ : ℕ}

/-- Bernoulli weights are nonnegative when `p ∈ [0,1]`. -/
theorem weight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

/-- The Bernoulli observation weights sum to 1. -/
theorem weights_sum_one (p : ℝ) :
    ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega = 1 := by
  classical
  have hpa := Fintype.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1 - p))
  simp only [add_sub_cancel, Finset.prod_const_one] at hpa
  rw [hpa]
  apply Finset.sum_congr rfl
  intro t _
  rw [bernoulliObservationWeight, Finset.prod_const, Finset.prod_const,
    Finset.card_compl]

/-- Edge case `t = 0`: if the `q`-moment is `0`, the event `|Z| ≤ 0` has prob ≥ 1 - failProb. -/
theorem tail_at_zero (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (q : ℕ) (hq : 1 ≤ q)
    (failProb : ℝ) (hfail : 0 ≤ failProb)
    (hmom0 : bernoulliExpectation p (fun Omega => |Z Omega| ^ q) ≤ 0) :
    bernoulliEventProb p (fun Omega => |Z Omega| ≤ 0) ≥ 1 - failProb := by
  classical
  -- each term w(Ω) * |Z Ω|^q ≥ 0, and the sum ≤ 0, so each term = 0
  have hterm_nn : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      0 ≤ bernoulliObservationWeight p Omega * |Z Omega| ^ q := by
    intro Omega
    have := weight_nonneg (n₁ := n₁) (n₂ := n₂) p hp0 hp1 Omega
    positivity
  have hsum0 : ∑ Omega : Finset (Fin n₁ × Fin n₂),
      bernoulliObservationWeight p Omega * |Z Omega| ^ q = 0 := by
    have hge : (0:ℝ) ≤ ∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega * |Z Omega| ^ q :=
      Finset.sum_nonneg (fun Omega _ => hterm_nn Omega)
    have hle : (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega * |Z Omega| ^ q) ≤ 0 := by
      unfold bernoulliExpectation at hmom0; exact hmom0
    linarith
  have heach : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      bernoulliObservationWeight p Omega * |Z Omega| ^ q = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun Omega _ => hterm_nn Omega)).1 hsum0
    intro Omega; exact h Omega (Finset.mem_univ _)
  -- For Ω with Z Ω ≠ 0, weight is 0; so prob of |Z|≤0 = sum over all = 1
  have hbe : bernoulliEventProb p (fun Omega => |Z Omega| ≤ 0)
      = ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega := by
    unfold bernoulliEventProb
    apply Finset.sum_congr rfl
    intro Omega _
    by_cases h : |Z Omega| ≤ 0
    · simp [h]
    · -- |Z Ω| > 0 ⇒ |Z Ω|^q > 0 ⇒ weight = 0
      push_neg at h
      have hZpos : 0 < |Z Omega| := h
      have hpowpos : 0 < |Z Omega| ^ q := by positivity
      have hw0 : bernoulliObservationWeight p Omega = 0 := by
        have := heach Omega
        rcases mul_eq_zero.1 this with h1 | h2
        · exact h1
        · exact absurd h2 (ne_of_gt hpowpos)
      simp [h, hw0]
  rw [hbe, weights_sum_one]
  linarith

end Prove3cbb

open Prove3cbb in
/-- `scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales` (3cbb6b11)
as a reduction onto the q-moment Bernstein core
`scalar_centered_sampling_qmoment_bernstein_estimate` and the proved Markov-tail
node `scalar_centered_sampling_markov_tail_from_qmoment_bound` (74ed00ae). -/
theorem solution :
    ∃ Cbern cbern : ℝ, 0 < Cbern ∧ 0 < cbern ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
        (B : Matrix (Fin n₁) (Fin n₂) ℝ)
        (entryScale frobScale : ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤ entryScale →
        frobeniusNorm B ≤ frobScale →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |Coeff Omega| ≤
                Cbern *
                  (Real.sqrt
                      ((β * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    frobScale +
                    ((β * Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    entryScale)) ≥
          1 - cbern * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Cbern, cbern, hCbern, hcbern, hcore⟩ :=
    scalar_centered_sampling_qmoment_bernstein_estimate
  refine ⟨Cbern, cbern, hCbern, hcbern, ?_⟩
  intro β hβ n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hentry hfrob
  -- abbreviations
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set n : ℝ := (↑(max n₁ n₂) : ℝ) with hn
  set T : ℝ := Cbern *
      (Real.sqrt ((β * Real.log n) / p) * frobScale +
        ((β * Real.log n) / p) * entryScale) with hT
  set failProb : ℝ := cbern * Real.rpow n (-β) with hfp
  -- p ∈ [0,1]
  have hn1n2 : (0:ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hp0 : 0 ≤ p := by
    rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp]
    rw [div_le_one hn1n2]
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hmle
    push_cast at this; linarith
  -- failProb ≥ 0
  have hnpos : (0:ℝ) < n := by
    rw [hn]; have : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _); exact_mod_cast this
  have hfail : 0 ≤ failProb := by
    rw [hfp]; apply mul_nonneg (le_of_lt hcbern); exact le_of_lt (Real.rpow_pos_of_pos hnpos _)
  -- get the moment bound from the core
  obtain ⟨q, hq, hmoment⟩ := hcore β hβ n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hentry hfrob
  -- fold the abbreviations into the obtained moment bound
  rw [← hp, ← hn, ← hT, ← hfp] at hmoment
  -- hmoment : bernoulliExpectation p (|Coeff|^q) ≤ T^q * failProb
  -- T ≥ 0
  have hlogn_nn : 0 ≤ Real.log n := by
    rw [hn]
    apply Real.log_nonneg
    have : 1 ≤ max n₁ n₂ := le_trans hn1 (le_max_left _ _)
    exact_mod_cast this
  have hbeta_log_nn : 0 ≤ β * Real.log n := mul_nonneg (by linarith) hlogn_nn
  have hbl_div_nn : 0 ≤ (β * Real.log n) / p := div_nonneg hbeta_log_nn hp0
  -- entrySupNorm, frobeniusNorm are nonneg, so the scales are nonneg
  have hentrySN_nn : 0 ≤ entrySupNorm B := by
    unfold entrySupNorm
    apply Real.iSup_nonneg
    intro i
    apply Real.iSup_nonneg
    intro j
    exact abs_nonneg _
  have hfrobN_nn : 0 ≤ frobeniusNorm B := by
    unfold frobeniusNorm; exact Real.sqrt_nonneg _
  have hentry_nn : 0 ≤ entryScale := le_trans hentrySN_nn hentry
  have hfrob_nn : 0 ≤ frobScale := le_trans hfrobN_nn hfrob
  have hbracket_nn : 0 ≤ Real.sqrt ((β * Real.log n) / p) * frobScale +
      ((β * Real.log n) / p) * entryScale := by
    apply add_nonneg
    · exact mul_nonneg (Real.sqrt_nonneg _) hfrob_nn
    · exact mul_nonneg hbl_div_nn hentry_nn
  have hT_nn : 0 ≤ T := by rw [hT]; exact mul_nonneg (le_of_lt hCbern) hbracket_nn
  -- (goal already folded into T / failProb by `set`)
  -- case split on T = 0 vs T > 0
  rcases eq_or_lt_of_le hT_nn with hT0 | hTpos
  · -- T = 0 edge: moment ≤ T^q * failProb = 0
    have hTeq : T = 0 := hT0.symm
    have hTq0 : T ^ q = 0 := by rw [hTeq]; exact zero_pow (by omega)
    have hmom0 : bernoulliExpectation p (fun Omega => |Coeff Omega| ^ q) ≤ 0 := by
      rw [hTq0, zero_mul] at hmoment; exact hmoment
    -- the target event |Coeff| ≤ T = 0
    have hres := tail_at_zero (n₁ := n₁) (n₂ := n₂) p hp0 hp1 Coeff q hq failProb hfail hmom0
    rw [hTeq]; exact hres
  · -- T > 0: apply the Markov tail node
    exact scalar_centered_sampling_markov_tail_from_qmoment_bound p hp0 hp1 Coeff q hq
      T failProb hTpos hfail hmoment
