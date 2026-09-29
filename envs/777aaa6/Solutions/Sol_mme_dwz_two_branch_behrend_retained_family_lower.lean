-- Prove2me | solution 1 for mme_dwz_two_branch_behrend_retained_family_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T14:51:35.738768+00:00
-- url     : https://prove2.me/submissions/80c8c0b0-4224-486e-9113-072f8d07da8d

import Mathlib
set_option autoImplicit false
set_option warningAsError true

private theorem common_prime_rate
    (A Z T d p : ℕ) (R Pa Pd Pz Pr xA xZ xd xp : ℝ)
    (hfactor : A = Z * T) (hdpos : 0 < d)
    (_hPa : 0 < Pa) (hPd : 0 < Pd) (_hPz : 0 < Pz) (hPr : 0 < Pr)
    (hA : Real.exp xA ≤ Pa * (A : ℝ))
    (hZ : Real.exp xZ ≤ Pz * (Z : ℝ))
    (hd : (d : ℝ) ≤ Pd * Real.exp xd)
    (hR : R = Pr * (T : ℝ) * Real.exp xp)
    (hp : (p : ℝ) ≤ 16 * max (d : ℝ) R) :
    (p : ℝ) * Real.exp (min (xA - xd) (xZ - xp)) ≤
      16 * max (Pa * Pd) (Pz * Pr) * (A : ℝ) := by
  let e : ℝ := Real.exp (min (xA - xd) (xZ - xp))
  let Q : ℝ := max (Pa * Pd) (Pz * Pr)
  have he : 0 ≤ e := (Real.exp_pos _).le
  have heA : e ≤ Real.exp (xA - xd) := by
    dsimp only [e]
    exact Real.exp_le_exp.mpr (min_le_left _ _)
  have heZ : e ≤ Real.exp (xZ - xp) := by
    dsimp only [e]
    exact Real.exp_le_exp.mpr (min_le_right _ _)
  have hQAP : Pa * Pd ≤ Q := le_max_left _ _
  have hQZP : Pz * Pr ≤ Q := le_max_right _ _
  have hdnonneg : (0 : ℝ) ≤ (d : ℝ) := by positivity
  have hTnonneg : (0 : ℝ) ≤ (T : ℝ) := by positivity
  have hAcast : (A : ℝ) = (Z : ℝ) * (T : ℝ) := by
    exact_mod_cast hfactor
  have hbranchA : e * (d : ℝ) ≤ Q * (A : ℝ) := by
    calc
      e * (d : ℝ) ≤ Real.exp (xA - xd) * (d : ℝ) :=
        mul_le_mul_of_nonneg_right heA hdnonneg
      _ ≤ Real.exp (xA - xd) * (Pd * Real.exp xd) :=
        mul_le_mul_of_nonneg_left hd (Real.exp_pos _).le
      _ = Pd * Real.exp xA := by
        rw [show Real.exp (xA - xd) * (Pd * Real.exp xd) =
          Pd * (Real.exp (xA - xd) * Real.exp xd) by ring,
          ← Real.exp_add]
        congr 2
        ring
      _ ≤ Pd * (Pa * (A : ℝ)) :=
        mul_le_mul_of_nonneg_left hA hPd.le
      _ = (Pa * Pd) * (A : ℝ) := by ring
      _ ≤ Q * (A : ℝ) :=
        mul_le_mul_of_nonneg_right hQAP (by positivity)
  have hbranchZ : e * R ≤ Q * (A : ℝ) := by
    rw [hR]
    calc
      e * (Pr * (T : ℝ) * Real.exp xp) ≤
          Real.exp (xZ - xp) * (Pr * (T : ℝ) * Real.exp xp) :=
        mul_le_mul_of_nonneg_right heZ (by positivity)
      _ = Pr * (T : ℝ) * Real.exp xZ := by
        rw [show Real.exp (xZ - xp) * (Pr * (T : ℝ) * Real.exp xp) =
          Pr * (T : ℝ) * (Real.exp (xZ - xp) * Real.exp xp) by ring,
          ← Real.exp_add]
        congr 2
        ring
      _ ≤ Pr * (T : ℝ) * (Pz * (Z : ℝ)) :=
        mul_le_mul_of_nonneg_left hZ (mul_nonneg hPr.le hTnonneg)
      _ = (Pz * Pr) * (A : ℝ) := by rw [hAcast]; ring
      _ ≤ Q * (A : ℝ) :=
        mul_le_mul_of_nonneg_right hQZP (by positivity)
  have hmax : e * max (d : ℝ) R ≤ Q * (A : ℝ) := by
    rcases le_total (d : ℝ) R with hdr | hrd
    · rw [max_eq_right hdr]
      exact hbranchZ
    · rw [max_eq_left hrd]
      exact hbranchA
  calc
    (p : ℝ) * e ≤ (16 * max (d : ℝ) R) * e :=
      mul_le_mul_of_nonneg_right hp he
    _ = 16 * (e * max (d : ℝ) R) := by ring
    _ ≤ 16 * (Q * (A : ℝ)) := by gcongr
    _ = 16 * Q * (A : ℝ) := by ring

theorem solution
    (A Z T d p I : ℕ) (R Pa Pd Pz Pr xA xZ xd xp : ℝ)
    (hfactor : A = Z * T)
    (hdpos : 0 < d) (hppos : 0 < p)
    (hPa : 0 < Pa) (hPd : 0 < Pd) (hPz : 0 < Pz) (hPr : 0 < Pr)
    (hA : Real.exp xA ≤ Pa * (A : ℝ))
    (hZ : Real.exp xZ ≤ Pz * (Z : ℝ))
    (hd : (d : ℝ) ≤ Pd * Real.exp xd)
    (hR : R = Pr * (T : ℝ) * Real.exp xp)
    (hp : (p : ℝ) ≤ 16 * max (d : ℝ) R)
    (hretained :
      ((T : ℝ) *
          (((p / 2 : ℕ) : ℝ) *
            Real.exp (-4 * Real.sqrt
              (Real.log (((p / 2 : ℕ) : ℝ)))))) /
          (2 * (p : ℝ) ^ 2) ≤ (I : ℝ)) :
    Real.exp (min (xA - xd) (xZ - xp)) *
          (((((p / 2 : ℕ) : ℝ) / (p : ℝ)) *
            Real.exp (-4 * Real.sqrt
              (Real.log (((p / 2 : ℕ) : ℝ)))))) /
          (32 * max (Pa * Pd) (Pz * Pr)) ≤
      (Z : ℝ) * (I : ℝ) := by
  let e : ℝ := Real.exp (min (xA - xd) (xZ - xp))
  let Q : ℝ := max (Pa * Pd) (Pz * Pr)
  let f : ℝ := ((p / 2 : ℕ) : ℝ)
  let b : ℝ := Real.exp (-4 * Real.sqrt (Real.log f))
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hppos
  have hQ : 0 < Q := (mul_pos hPa hPd).trans_le (le_max_left _ _)
  have hf : 0 ≤ f := by positivity
  have hb : 0 < b := Real.exp_pos _
  have hprime := common_prime_rate A Z T d p R Pa Pd Pz Pr
    xA xZ xd xp hfactor hdpos hPa hPd hPz hPr hA hZ hd hR hp
  change (p : ℝ) * e ≤ 16 * Q * (A : ℝ) at hprime
  have hdiv : e / (16 * Q) ≤ (A : ℝ) / (p : ℝ) := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num) hQ) hpR).2
    nlinarith
  have hscaleNonneg : 0 ≤ f * b / (2 * (p : ℝ)) := by positivity
  have hscaled := mul_le_mul_of_nonneg_right hdiv hscaleNonneg
  have hfactorR : (A : ℝ) = (Z : ℝ) * (T : ℝ) := by
    exact_mod_cast hfactor
  have hretainedZ := mul_le_mul_of_nonneg_left hretained
    (show (0 : ℝ) ≤ (Z : ℝ) by positivity)
  change (T : ℝ) * (f * b) / (2 * (p : ℝ) ^ 2) ≤ (I : ℝ)
    at hretained
  change (Z : ℝ) * ((T : ℝ) * (f * b) /
      (2 * (p : ℝ) ^ 2)) ≤ (Z : ℝ) * (I : ℝ) at hretainedZ
  have hfinal : e * (((f / (p : ℝ)) * b) / (32 * Q)) ≤
      (Z : ℝ) * (I : ℝ) := by
    calc
      e * (((f / (p : ℝ)) * b) / (32 * Q)) =
          (e / (16 * Q)) * (f * b / (2 * (p : ℝ))) := by
            field_simp
            ; ring
      _ ≤ ((A : ℝ) / (p : ℝ)) *
          (f * b / (2 * (p : ℝ))) := hscaled
      _ = (Z : ℝ) * ((T : ℝ) * (f * b) /
          (2 * (p : ℝ) ^ 2)) := by
            rw [hfactorR]
            field_simp
      _ ≤ (Z : ℝ) * (I : ℝ) := hretainedZ
  dsimp only [e, Q, f, b] at hfinal
  convert hfinal using 1
  all_goals ring
