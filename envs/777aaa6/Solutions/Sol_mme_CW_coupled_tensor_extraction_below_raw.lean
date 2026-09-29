-- Prove2me | solution 1 for mme_CW_coupled_tensor_extraction_below_raw
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-09-07T14:52:23.027474+00:00
-- url     : https://prove2.me/submissions/30c5f5ae-9e9e-4f86-9f63-f5f281039ef4

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_tensor_quotient
import Theorems.Thm_mme_CW_primary_hash_Ctensor_outer_middle_certificates
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
import Theorems.Thm_mme_cyclicSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_CW_primary_profile_capacity_quarter_root
import Theorems.Thm_mme_MM_induced_matching_quarter_root_absorption

open MME BigOperators Filter

universe u

set_option autoImplicit false

/-- The quarter-root loss `(√√(N+1))⁻¹` tends to zero. -/
theorem ext_quarter_root_loss_tendsto_zero :
    Tendsto (fun N : ℕ => (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹)
      atTop (nhds 0) := by
  have h1 : Tendsto (fun N : ℕ => (((N + 1 : ℕ) : ℝ))) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hs : Tendsto (fun x : ℝ => Real.sqrt x) atTop atTop := by
    have : (fun x : ℝ => Real.sqrt x) = fun x : ℝ => x ^ ((1 : ℝ) / 2) := by
      funext x; exact Real.sqrt_eq_rpow x
    rw [this]
    exact tendsto_rpow_atTop (by norm_num)
  have h2 : Tendsto (fun N : ℕ => Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))
      atTop atTop := hs.comp (hs.comp h1)
  exact h2.inv_tendsto_atTop

/-- The real-number bookkeeping of the extraction: capacity, absorption of the
quarter-root loss, and the strict sub-base. -/
theorem ext_coupled_extraction_weight_bound
    (V raw loss S : ℝ) (N A H k Z X B : ℕ)
    (hV : 0 ≤ V) (hS : 0 ≤ S) (hX : 0 < X)
    (hVN : V ≤ raw * Real.exp (-loss))
    (hA : (Z : ℝ) * Real.exp (-((N : ℝ) * loss / 12)) ≤ (A : ℝ))
    (hH : (B : ℝ) * Real.exp (-((N : ℝ) * loss / 8)) ≤ 4 * (X : ℝ) ^ 2 * (H : ℝ))
    (hcap : (raw * Real.exp (-(loss / 2))) ^ (2 * N) ≤
      (((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4) *
        Real.exp (-((N : ℝ) * loss / 2))) * S)
    (habs : (H : ℝ) ^ 2 * Real.exp (-((N : ℝ) * loss)) ≤
      (H : ℝ) ^ 2 * Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ)))))
    (hk : (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
      Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))) ≤ (k : ℝ)) :
    V ^ (2 * N) ≤ (k : ℝ) * S := by
  have hXr : (0 : ℝ) < (X : ℝ) := by exact_mod_cast hX
  have hpow : V ^ (2 * N) ≤ (raw * Real.exp (-loss)) ^ (2 * N) :=
    pow_le_pow_left₀ hV hVN _
  have hsplit : (raw * Real.exp (-loss)) ^ (2 * N) =
      (raw * Real.exp (-(loss / 2))) ^ (2 * N) * Real.exp (-((N : ℝ) * loss)) := by
    rw [mul_pow, mul_pow, ← Real.exp_nat_mul, ← Real.exp_nat_mul, mul_assoc,
      ← Real.exp_add]
    congr 2
    push_cast
    ring
  have hexp : Real.exp (-((N : ℝ) * loss / 12)) ^ 3 *
      Real.exp (-((N : ℝ) * loss / 8)) ^ 2 = Real.exp (-((N : ℝ) * loss / 2)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have h1 : ((Z : ℝ) * Real.exp (-((N : ℝ) * loss / 12))) ^ 3 ≤ (A : ℝ) ^ 3 :=
    pow_le_pow_left₀ (by positivity) hA 3
  have h2 : ((B : ℝ) * Real.exp (-((N : ℝ) * loss / 8))) ^ 2 ≤
      (4 * (X : ℝ) ^ 2 * (H : ℝ)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hH 2
  have h3 := mul_le_mul h1 h2 (by positivity) (by positivity)
  have hcapA : ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4) *
      Real.exp (-((N : ℝ) * loss / 2)) ≤ (A : ℝ) ^ 3 * (H : ℝ) ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    rw [← hexp]
    have : (Z : ℝ) ^ 3 * (B : ℝ) ^ 2 *
        (Real.exp (-((N : ℝ) * loss / 12)) ^ 3 * Real.exp (-((N : ℝ) * loss / 8)) ^ 2) =
        ((Z : ℝ) * Real.exp (-((N : ℝ) * loss / 12))) ^ 3 *
          ((B : ℝ) * Real.exp (-((N : ℝ) * loss / 8))) ^ 2 := by ring
    rw [this]
    calc ((Z : ℝ) * Real.exp (-((N : ℝ) * loss / 12))) ^ 3 *
          ((B : ℝ) * Real.exp (-((N : ℝ) * loss / 8))) ^ 2
        ≤ (A : ℝ) ^ 3 * (4 * (X : ℝ) ^ 2 * (H : ℝ)) ^ 2 := h3
      _ = (A : ℝ) ^ 3 * (H : ℝ) ^ 2 * (16 * (X : ℝ) ^ 4) := by ring
  have hE : 0 ≤ Real.exp (-((N : ℝ) * loss)) := (Real.exp_pos _).le
  calc V ^ (2 * N) ≤ (raw * Real.exp (-loss)) ^ (2 * N) := hpow
    _ = (raw * Real.exp (-(loss / 2))) ^ (2 * N) * Real.exp (-((N : ℝ) * loss)) := hsplit
    _ ≤ ((((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4) *
          Real.exp (-((N : ℝ) * loss / 2))) * S) * Real.exp (-((N : ℝ) * loss)) :=
        mul_le_mul_of_nonneg_right hcap hE
    _ = (((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4) *
          Real.exp (-((N : ℝ) * loss / 2))) * Real.exp (-((N : ℝ) * loss)) * S := by ring
    _ ≤ ((A : ℝ) ^ 3 * (H : ℝ) ^ 2) * Real.exp (-((N : ℝ) * loss)) * S :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcapA hE) hS
    _ = (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 * Real.exp (-((N : ℝ) * loss))) * S := by ring
    _ ≤ (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
          Real.exp (-100 * Real.sqrt (Real.log (((H + 1 : ℕ) : ℝ))))) * S :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left habs (by positivity)) hS
    _ ≤ (k : ℝ) * S := mul_le_mul_of_nonneg_right hk hS

theorem solution
    {K : Type u} [Field K] (q : ℕ) (hq : 3 ≤ q)
    (tau : ℝ) (htau : 2 ≤ 3 * tau)
    (V : ℝ) (hV : 0 ≤ V)
    (hVlt :
      V < 4 * (q : ℝ) ^ (3 * tau) *
        ((q : ℝ) ^ (3 * tau) + 2)) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((q : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let G : ℕ := N - L
      (0 < L ∧ 0 < G ∧ L + G = N ∧ 341 * L < 100 * G) →
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i => MMObj K (a i) (b i) (c i)))
          ((cyclicSymmetrization (coupledObj K q)).kronPow (2 * N)) ∧
        V ^ (2 * N) ≤
          ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  have hq0 : (0 : ℝ) < (q : ℝ) := by
    have : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    linarith
  have hraw_pos : (0 : ℝ) < 4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2) := by
    positivity
  have hV_ev : ∀ᶠ N : ℕ in atTop,
      V ≤ (4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2)) *
        Real.exp (-(Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹) := by
    rcases hV.lt_or_eq with hVpos | hV0
    · have hlogpos : 0 < Real.log
          ((4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2)) / V) := by
        apply Real.log_pos
        rw [one_lt_div hVpos]; exact hVlt
      have hev := ext_quarter_root_loss_tendsto_zero.eventually (gt_mem_nhds hlogpos)
      filter_upwards [hev] with N hN
      have hdiv : V / (4 * (q : ℝ) ^ (3 * tau) * ((q : ℝ) ^ (3 * tau) + 2)) ≤
          Real.exp (-(Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹) := by
        rw [← Real.log_le_iff_le_exp (div_pos hVpos hraw_pos)]
        rw [Real.log_div hVpos.ne' hraw_pos.ne']
        rw [Real.log_div hraw_pos.ne' hVpos.ne'] at hN
        linarith
      rwa [div_le_iff₀ hraw_pos, mul_comm] at hdiv
    · filter_upwards with N
      rw [← hV0]; positivity
  filter_upwards [mme_CW_primary_hash_Ctensor_outer_middle_certificates (K := K) q tau,
    mme_CW_primary_profile_capacity_quarter_root q hq tau htau,
    mme_MM_induced_matching_quarter_root_absorption, hV_ev] with N hcert hcap habs hVN
  intro lambda L G hyp
  obtain ⟨hL, hG, hLG, hratio⟩ := hyp
  obtain ⟨A, H, hHpos, hHle, ⟨stars⟩, hA, hH⟩ := hcert ⟨hL, hLG, hratio⟩
  have hcap' := hcap ⟨hL, hG, hLG⟩
  have habs' := habs H hHpos hHle
  obtain ⟨k, a, b, c, hres, hk, hvol⟩ :=
    mme_Ctensor_one_H_one_outer_family_direct_finite_extraction stars hHpos
  refine ⟨k, a, b, c,
    TensorObj.Restrict.trans hres
      (mme_cyclicSymmetrization_kronPow_isomorphic (coupledObj K q) (2 * N)).2, ?_⟩
  have hX : 0 < Nat.choose N (N - L) := Nat.choose_pos (Nat.sub_le N L)
  have hmain := ext_coupled_extraction_weight_bound V _ _ _ N A H k _ _ _
    hV (by positivity) hX hVN hA hH hcap' habs' hk
  have hsum : ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) =
      (k : ℝ) * (((((q ^ (4 * G + 2 * L)) ^ 3 : ℕ)) : ℝ) ^ tau) := by
    simp only [hvol, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    try rfl
  rw [hsum]
  have hcube : ((q ^ (4 * G + 2 * L)) ^ 3 : ℕ) =
      (q ^ (4 * G + 2 * L)) * (q ^ (4 * G + 2 * L)) * (q ^ (4 * G + 2 * L)) := by
    ring
  rw [hcube]
  exact hmain
