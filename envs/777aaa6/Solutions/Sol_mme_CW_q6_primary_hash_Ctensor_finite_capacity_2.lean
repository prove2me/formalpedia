-- Prove2me | solution 2 for mme_CW_q6_primary_hash_Ctensor_finite_capacity
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:38:33.973382+00:00
-- url     : https://prove2.me/submissions/37aa0751-b0b3-4be8-b19e-b573947babe5

import Definitions.Def_CTensorOneHOneFamilyCertificate
import Definitions.Def_mme_CW_q6_primary_hash_family
import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_tensor_bridge
import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
import Theorems.Thm_mme_CW_q6_primary_capacity_of_outer_middle_fibers
import Theorems.Thm_mme_CW_q6_primary_hash_family_uniform_MM_dimensions
import Theorems.Thm_mme_Ctensor_uniform_outer_family_square_extraction
import Theorems.Thm_mme_cyclicSymmetrization_kronPow_isomorphic
import Theorems.Thm_mme_CW_q6_coupled_survivor_square_isomorphic
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_bigAdd_prefix_restrict
import Mathlib.Tactic

open MME BigOperators Filter
universe u
set_option autoImplicit false

/-- Selecting a cubical number of copies loses at most a factor of eight. -/
private theorem cube_prefix_eighth (k : ℕ) :
    ∃ A : ℕ, A ^ 3 ≤ k ∧ k ≤ 8 * A ^ 3 := by
  by_cases hk : k = 0
  · subst k
    exact ⟨0, by norm_num, by norm_num⟩
  let A := Nat.findGreatest (fun a ↦ a ^ 3 ≤ k) k
  have hA : 1 ≤ A := Nat.le_findGreatest (P := fun a ↦ a ^ 3 ≤ k) (by omega) (by simpa using Nat.one_le_iff_ne_zero.mpr hk)
  have hAk : A ^ 3 ≤ k := Nat.findGreatest_spec (P := fun a ↦ a ^ 3 ≤ k) (Nat.zero_le k) (by simp)
  have hnext : k < (A + 1) ^ 3 := by
    by_contra hn
    have hp : (A + 1) ^ 3 ≤ k := by omega
    have hb : A + 1 ≤ k := (le_self_pow (by omega) (by norm_num : (3 : ℕ) ≠ 0)).trans hp
    have := Nat.le_findGreatest (P := fun a ↦ a ^ 3 ≤ k) hb hp
    change A + 1 ≤ A at this
    omega
  refine ⟨A, hAk, ?_⟩
  have hbound : (A + 1) ^ 3 ≤ (2 * A) ^ 3 := by
    gcongr
    omega
  calc
    k ≤ (A + 1) ^ 3 := hnext.le
    _ ≤ (2 * A) ^ 3 := hbound
    _ = 8 * A ^ 3 := by ring


private theorem behrend_loss_bound (N H : ℕ) (hH : H ≤ 4 ^ N) :
    Real.exp (-200 * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
      Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ))) := by
  have hp : H + 1 ≤ 4 ^ (N + 1) := by
    have hpos : 0 < 4 ^ N := by positivity
    rw [pow_succ]
    omega
  have hlog : Real.log ((H + 1 : ℕ) : ℝ) ≤ 4 * ((N + 1 : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((H + 1 : ℕ) : ℝ))
      (show ((H + 1 : ℕ) : ℝ) ≤ (4 : ℝ) ^ (N + 1) by exact_mod_cast hp)
    rw [Real.log_pow] at h
    have hfour : Real.log (4 : ℝ) ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) * Real.log 4 := h
      _ ≤ ((N + 1 : ℕ) : ℝ) * 4 := mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = _ := mul_comm _ _
  have hl0 : 0 ≤ Real.log ((H + 1 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hs : Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt hl0,
      Real.sq_sqrt (show (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by positivity),
      Real.sqrt_nonneg (Real.log ((H + 1 : ℕ) : ℝ)),
      Real.sqrt_nonneg ((N + 1 : ℕ) : ℝ)]
  apply Real.exp_le_exp.mpr
  linarith


private theorem quarter_root_loss_bound (N : ℕ) (D : ℝ)
    (hN : 1 ≤ N)
    (hroot : 4 * (D + Real.log 8) ≤ Real.sqrt (Real.sqrt ((N + 1 : ℕ) : ℝ))) :
    Real.log 8 + -((N : ℝ) * (Real.sqrt (Real.sqrt ((N + 1 : ℕ) : ℝ)))⁻¹ / 2) ≤
      -D * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
  let E : ℝ := D + Real.log 8
  let u : ℝ := Real.sqrt ((N + 1 : ℕ) : ℝ)
  let t : ℝ := Real.sqrt u
  have hlog : 0 ≤ Real.log (8 : ℝ) := Real.log_nonneg (by norm_num)
  have hu : 0 < u := by dsimp [u]; positivity
  have ht : 0 < t := by dsimp [t]; positivity
  have hu_sq : u ^ 2 = ((N + 1 : ℕ) : ℝ) := Real.sq_sqrt (by positivity)
  have ht_sq : t ^ 2 = u := Real.sq_sqrt hu.le
  have hn : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by
    exact_mod_cast (show N + 1 ≤ 2 * N by omega)
  have hEt : 4 * E * t ≤ u := by
    have hh := mul_le_mul_of_nonneg_right hroot ht.le
    nlinarith only [hh, ht_sq]
  have hprod := mul_le_mul_of_nonneg_right hEt hu.le
  have hbudget : 2 * E * u * t ≤ (N : ℝ) := by nlinarith only [hprod, hu_sq, hn]
  have hu1 : 1 ≤ u := by
    have : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N)
    nlinarith only [this, hu_sq, hu]
  have hlogscale : Real.log (8 : ℝ) ≤ Real.log 8 * u :=
    le_mul_of_one_le_right hlog hu1
  change Real.log 8 + -((N : ℝ) * t⁻¹ / 2) ≤ -D * u
  have hscaled := mul_le_mul_of_nonneg_right hlogscale ht.le
  apply (mul_le_mul_iff_of_pos_right ht).mp
  field_simp
  dsimp [E] at hbudget
  nlinarith only [hbudget, hscaled]


private theorem capacity_sqrt_lower (N Z X B A H : ℕ) (C u : ℝ)
    (hn0 : (N : ℝ) ≠ 0) (hX : 0 < X) (hC : 0 ≤ C) (hu : 0 < u)
    (houter : (Z : ℝ) * Real.exp (-C * u) ≤ (A : ℝ))
    (hmiddle : (B : ℝ) * Real.exp (-C * u) ≤ 4 * (X : ℝ) ^ 2 * (H : ℝ)) :
    (((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4)) *
      Real.exp (-(6 * C * u)) ≤ ((A ^ 3 : ℕ) : ℝ) * (H : ℝ) ^ 2 := by
  have harg12 : (N : ℝ) * (12 * C * u / N) / 12 = C * u := by
    field_simp
  have harg8 : C * u ≤ (N : ℝ) * (12 * C * u / N) / 8 := by
    have heq : (N : ℝ) * (12 * C * u / N) / 8 = 3 / 2 * (C * u) := by
      field_simp
      ring
    rw [heq]
    nlinarith only [mul_nonneg hC hu.le]
  have harg2 : (N : ℝ) * (12 * C * u / N) / 2 = 6 * C * u := by
    field_simp
    ring
  have hh := mme_CW_q6_primary_capacity_of_outer_middle_fibers
    N Z X B A H (12 * C * u / N) hX
    (by simpa only [harg12, neg_mul] using houter)
    (by
      calc
        (B : ℝ) * Real.exp (-((N : ℝ) * (12 * C * u / N) / 8)) ≤
            (B : ℝ) * Real.exp (-C * u) := by
          gcongr
          linarith
        _ ≤ _ := hmiddle)
  simpa only [harg2] using hh


theorem solution
    {K : Type u} [Field K]
    (tau : ℝ) (htau : 2 ≤ 3 * tau) :
    ∀ᶠ N : ℕ in atTop,
      let lambda : ℝ := 2 / ((6 : ℝ) ^ (3 * tau) + 2)
      let L : ℕ := ⌊lambda * (N : ℝ)⌋₊
      let Gcount : ℕ := N - L
      let Zcount : ℕ :=
        Nat.choose (2 * N) L * Nat.choose (2 * N - L) L
      let Xcount : ℕ := Nat.choose N Gcount
      let middle : ℕ := Nat.choose (2 * Gcount) Gcount
      let capacity : ℝ :=
        ((Zcount : ℝ) ^ 3 * (middle : ℝ) ^ 2) /
          (16 * (Xcount : ℝ) ^ 4)
      let loss : ℝ :=
        (Real.sqrt (Real.sqrt (((N + 1 : ℕ) : ℝ))))⁻¹
      (0 < L ∧ L + Gcount = N ∧ 341 * L < 100 * Gcount) →
      ∃ A H : ℕ,
        0 < H ∧
        H ≤ 4 ^ N ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun _ : Fin (A ^ 3) =>
            TensorObj.kron (MMObj K H H H)
              (coupledQ6Survivor K L Gcount)))
          ((cyclicSymmetrization (coupledObj K 6)).kronPow (2 * N)) ∧
        capacity * Real.exp (-((N : ℝ) * loss / 2)) ≤
          ((A ^ 3 : ℕ) : ℝ) * ((H : ℝ) ^ 2) := by
  classical
  let L : ℕ → ℕ := fun N ↦ ⌊2 / ((6 : ℝ) ^ (3 * tau) + 2) * (N : ℝ)⌋₊
  let G : ℕ → ℕ := fun N ↦ N - L N
  obtain ⟨C, hC, hstars⟩ := mme_CW_q6_primary_hash_uniform_stars_sqrt_loss L G
  let D : ℝ := 6 * C + 200
  let E : ℝ := D + Real.log 8
  have hnat : Tendsto (fun N : ℕ ↦ ((N + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hroot : Tendsto (fun N : ℕ ↦ Real.sqrt (Real.sqrt ((N + 1 : ℕ) : ℝ)))
      atTop atTop := Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp hnat)
  filter_upwards [hstars, eventually_ge_atTop (1 : ℕ), hroot.eventually_ge_atTop (4 * E)]
    with N hstars hN hroot
  dsimp only
  intro hprofile
  change 0 < L N ∧ L N + G N = N ∧ 341 * L N < 100 * G N at hprofile
  obtain ⟨A₀, H₀, family, hH, houter, hmiddle⟩ := hstars hprofile
  let Z : ℕ := Nat.choose (2 * N) (L N) * Nat.choose (2 * N - L N) (L N)
  let X : ℕ := Nat.choose N (G N)
  let B : ℕ := Nat.choose (2 * G N) (G N)
  let cap : ℝ := ((Z : ℝ) ^ 3 * (B : ℝ) ^ 2) / (16 * (X : ℝ) ^ 4)
  let u : ℝ := Real.sqrt ((N + 1 : ℕ) : ℝ)
  let t : ℝ := Real.sqrt u
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  have hX : 0 < X := Nat.choose_pos (by dsimp [G]; omega)
  have hu : 0 < u := by dsimp [u]; positivity
  have hcap : cap * Real.exp (-(6 * C * u)) ≤
      ((A₀ ^ 3 : ℕ) : ℝ) * (H₀ : ℝ) ^ 2 :=
    capacity_sqrt_lower N Z X B A₀ H₀ C u hn0 hX hC hu houter hmiddle
  obtain ⟨cert, hdims⟩ := mme_CW_q6_primary_hash_family_uniform_MM_dimensions
    (K := K) N (L N) (G N) A₀ H₀ family
  obtain ⟨k, hr, hk⟩ := mme_Ctensor_uniform_outer_family_square_extraction cert
    (6 ^ (2 * G N)) (6 ^ (2 * L N)) (6 ^ (2 * G N)) hdims family.hHpos
  let s : ℕ := 6 ^ (4 * G N + 2 * L N)
  have hshape : 6 ^ (2 * G N) * 6 ^ (2 * L N) * 6 ^ (2 * G N) = s := by
    dsimp [s]
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hshape] at hr
  have hcount : ((A₀ ^ 3 : ℕ) : ℝ) * (H₀ : ℝ) ^ 2 *
      Real.exp (-200 * u) ≤ (k : ℝ) := by
    calc
      _ ≤ ((A₀ ^ 3 : ℕ) : ℝ) * (H₀ : ℝ) ^ 2 *
          Real.exp (-100 * Real.sqrt (Real.log ((H₀ + 1 : ℕ) : ℝ))) :=
        mul_le_mul_of_nonneg_left (behrend_loss_bound N H₀ hH) (by positivity)
      _ ≤ _ := by simpa only [Nat.cast_pow, mul_assoc] using hk
  have hkcap : cap * Real.exp (-D * u) ≤ (k : ℝ) := by
    calc
      _ = (cap * Real.exp (-(6 * C * u))) * Real.exp (-200 * u) := by
        rw [show -D * u = -(6 * C * u) + -200 * u by dsimp [D]; ring,
          Real.exp_add]
        ring
      _ ≤ (((A₀ ^ 3 : ℕ) : ℝ) * (H₀ : ℝ) ^ 2) * Real.exp (-200 * u) :=
        mul_le_mul_of_nonneg_right hcap (Real.exp_nonneg _)
      _ ≤ _ := hcount
  obtain ⟨A, hAk, hkA⟩ := cube_prefix_eighth k
  let S : TensorObj K 3 := coupledQ6Survivor K (L N) (G N)
  have hunit : TensorObj.Isomorphic (TensorObj.kron (MMObj K 1 1 1) S) S := by
    apply TensorQ.toQ_eq_iff.mp
    rw [TensorQ.toQ_kron]
    change MMq K 1 1 1 * TensorQ.toQ S = TensorQ.toQ S
    rw [MMq_one, one_mul]
  have hblock : TensorObj.Restrict (TensorObj.kron (MMObj K 1 1 1) S)
      (MMObj K s s s) :=
    hunit.1.trans (mme_CW_q6_coupled_survivor_square_isomorphic (K := K) (L N) (G N)).1
  have hpref := mme_bigAdd_prefix_restrict (K := K) (d := 3) (by omega)
    hAk (fun _ : Fin k ↦ MMObj K s s s)
  have hHbound : 1 ≤ (4 : ℕ) ^ N := by
    have hp : 0 < (4 : ℕ) ^ N := by positivity
    omega
  refine ⟨A, 1, by norm_num, hHbound,
    (mme_bigAdd_mono_restrict (fun _ : Fin (A ^ 3) ↦ hblock)).trans
      (hpref.trans (hr.trans
        (mme_cyclicSymmetrization_kronPow_isomorphic (coupledObj K 6) (2 * N)).2)), ?_⟩
  simp only [Nat.cast_one, one_pow, mul_one]
  change cap * Real.exp (-((N : ℝ) * t⁻¹ / 2)) ≤ ((A ^ 3 : ℕ) : ℝ)
  have hexparg : Real.log 8 + -((N : ℝ) * t⁻¹ / 2) ≤ -D * u :=
    quarter_root_loss_bound N D hN hroot
  have hloss : 8 * (cap * Real.exp (-((N : ℝ) * t⁻¹ / 2))) ≤
      cap * Real.exp (-D * u) := by
    have he := Real.exp_le_exp.mpr hexparg
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 8)] at he
    have hh := mul_le_mul_of_nonneg_left he (show 0 ≤ cap by dsimp [cap]; positivity)
    rw [mul_left_comm cap 8] at hh
    exact hh
  have hkcast : (k : ℝ) ≤ 8 * ((A ^ 3 : ℕ) : ℝ) := by exact_mod_cast hkA
  apply (mul_le_mul_iff_of_pos_left (by norm_num : (0 : ℝ) < 8)).mp
  exact hloss.trans (hkcap.trans hkcast)

#print axioms solution
