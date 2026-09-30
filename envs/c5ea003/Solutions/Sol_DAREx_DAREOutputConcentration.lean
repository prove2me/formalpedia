-- Prove2me | solution 1 for DAREx.DAREOutputConcentration
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-09-29T19:50:15.044585+00:00
-- url     : https://prove2.me/submissions/ec1ba3f1-a9c1-4311-9599-d4e6a473b07d

import Definitions.Def_DAREx_Model
import Theorems.Thm_DAREx_DAREExponentialTail
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section

open scoped BigOperators
open DAREx

private lemma concentration_energy_identity (n : ℕ) (c : Fin n → ℝ) (hn : 0 < n) :
    energy c = (n : ℝ) * (empiricalMean c ^ 2 + empiricalVariance c) := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  unfold empiricalVariance empiricalMean coefficientSum energy
  simp_rw [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

private lemma concentration_phi_pos {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    0 < phi p := by
  unfold phi
  split_ifs with hhalf
  · norm_num
  · rcases lt_or_gt_of_ne hhalf with hlow | hhigh
    · apply div_pos
      · linarith
      · apply Real.log_pos
        apply (lt_div_iff₀ hp).2
        linarith
    · apply div_pos_of_neg_of_neg
      · linarith
      · apply Real.log_neg
        · exact div_pos (sub_pos.mpr hp') hp
        · apply (div_lt_iff₀ hp).2
          linarith

private lemma concentration_probability_complement {n : ℕ} (p t : ℝ)
    (f : Mask n → ℝ) :
    probability p (fun ω ↦ |f ω| ≤ t) + probability p (fun ω ↦ t < |f ω|) = 1 := by
  classical
  unfold probability
  rw [← Finset.sum_add_distrib, ← maskMass_sum (n := n) p]
  apply Finset.sum_congr rfl
  intro ω _
  by_cases h : |f ω| ≤ t
  · simp [h, not_lt.mpr h]
  · simp [h, lt_of_not_ge h]

private lemma concentration_energy_nonneg {n : ℕ} (c : Fin n → ℝ) : 0 ≤ energy c :=
  Finset.sum_nonneg (fun j _ ↦ sq_nonneg (c j))

private lemma concentration_zero_coefficients {n : ℕ} (c : Fin n → ℝ)
    (hQ : energy c = 0) : ∀ j, c j = 0 := by
  have hzero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) ↦ sq_nonneg (c j))).1 hQ
  intro j
  exact (sq_eq_zero_iff).1 (hzero j (Finset.mem_univ j))

private lemma concentration_from_tail
    (n : ℕ) (c : Fin n → ℝ) (p γ : ℝ)
    (henergy : energy c = (n : ℝ) * (empiricalMean c ^ 2 + empiricalVariance c))
    (htail : ∀ t : ℝ, 0 < energy c → 0 < t →
      probability p (fun ω ↦ t < |dareError p c ω|) ≤
        2 * Real.exp (-(t ^ 2 * (1 - p) ^ 2 / (phi p * energy c))))
    (hp : 0 < p) (hp' : p < 1) (hγ : 0 < γ) (hγ' : γ < 1) :
    1 - γ ≤ probability p (fun ω ↦ |dareError p c ω| ≤
      Real.sqrt (phi p) / (1 - p) *
        Real.sqrt ((n : ℝ) * (empiricalMean c ^ 2 + empiricalVariance c)) *
        Real.sqrt (Real.log (2 / γ))) := by
  classical
  rw [← henergy]
  by_cases hQ : energy c = 0
  · have hc := concentration_zero_coefficients c hQ
    have herror : ∀ ω : Mask n, dareError p c ω = 0 := by
      intro ω
      simp [dareError, outputError, hc]
    have hprob : probability p (fun ω ↦ |dareError p c ω| ≤
        Real.sqrt (phi p) / (1 - p) * Real.sqrt (energy c) *
          Real.sqrt (Real.log (2 / γ))) = 1 := by
      simp [probability, herror, hQ, maskMass_sum]
    rw [hprob]
    linarith
  · have hQpos : 0 < energy c := lt_of_le_of_ne (concentration_energy_nonneg c) (Ne.symm hQ)
    have hphi := concentration_phi_pos hp hp'
    have hden : 0 < 1 - p := sub_pos.mpr hp'
    have hlog : 0 < Real.log (2 / γ) := by
      apply Real.log_pos
      apply (lt_div_iff₀ hγ).2
      linarith
    let t := Real.sqrt (phi p) / (1 - p) * Real.sqrt (energy c) *
      Real.sqrt (Real.log (2 / γ))
    have ht : 0 < t := mul_pos
      (mul_pos (div_pos (Real.sqrt_pos.2 hphi) hden) (Real.sqrt_pos.2 hQpos))
      (Real.sqrt_pos.2 hlog)
    have hexponent : t ^ 2 * (1 - p) ^ 2 / (phi p * energy c) = Real.log (2 / γ) := by
      dsimp [t]
      rw [mul_pow, mul_pow, div_pow, Real.sq_sqrt hphi.le, Real.sq_sqrt hQpos.le,
        Real.sq_sqrt hlog.le]
      field_simp
    have hbound : 2 * Real.exp (-Real.log (2 / γ)) = γ := by
      rw [Real.exp_neg, Real.exp_log (div_pos (by norm_num) hγ)]
      field_simp
    have hbad : probability p (fun ω ↦ t < |dareError p c ω|) ≤ γ := by
      have h := htail t hQpos ht
      rw [hexponent, hbound] at h
      exact h
    have hcompl := concentration_probability_complement p t (dareError p c)
    change 1 - γ ≤ probability p (fun ω ↦ |dareError p c ω| ≤ t)
    linarith

-- Deng et al., Appendix E.1, PDF p. 30, equation (8), and PDF p. 31 energy identity.
-- The existing exponential-tail theorem is the only conditional dependency.
theorem solution :
    ∀ (n : ℕ) (c : Fin n → ℝ) (p γ : ℝ),
      0 < n → 0 < p → p < 1 → 0 < γ → γ < 1 →
      1 - γ ≤ probability p (fun ω ↦ |dareError p c ω| ≤
        Real.sqrt (phi p) / (1 - p) *
          Real.sqrt ((n : ℝ) * (empiricalMean c ^ 2 + empiricalVariance c)) *
          Real.sqrt (Real.log (2 / γ))) := by
  intro n c p γ hn hp hp' hγ hγ'
  exact concentration_from_tail n c p γ (concentration_energy_identity n c hn)
    (fun t hQ ht ↦ DAREExponentialTail n c p t hp hp' hQ ht) hp hp' hγ hγ'
