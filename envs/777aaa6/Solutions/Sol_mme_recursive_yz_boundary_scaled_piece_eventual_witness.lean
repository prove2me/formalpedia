-- Prove2me | solution 1 for mme_recursive_yz_boundary_scaled_piece_eventual_witness
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T10:41:14.964821+00:00
-- url     : https://prove2.me/submissions/907eda17-321d-4c4c-8f66-e35f490f512d

import Definitions.Def_mme_recursive_yz_boundary_data
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_tensor_quotient
import Theorems.Thm_mme_recursive_yz_boundary_actual_matrix_extraction
import Theorems.Thm_mme_sixSymmetrization_MMObj_isomorphic
import Theorems.Thm_mme_sixSymmetrization_restrict
import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open BigOperators Filter MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.Boundary
  MME.CompleteSplit MME.DWZRestrictedValue

universe u

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace MME.DWZBoundaryValue

theorem const_add_sqrt_le (A B c : ℝ) (hc : 0 < c) :
    ∀ᶠ t : ℕ in atTop, A + B * Real.sqrt t ≤ c * t := by
  set K := |A| + |B| with hK
  have hK0 : 0 ≤ K := by positivity
  filter_upwards [eventually_ge_atTop (⌈(K / c) ^ 2⌉₊ + 1)] with t ht
  have ht1 : (1 : ℝ) ≤ t := by
    have : 1 ≤ t := le_trans (Nat.le_add_left 1 _) ht
    exact_mod_cast this
  have hsq1 : 1 ≤ Real.sqrt t := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt ht1
  have hKc : K / c ≤ Real.sqrt t := by
    have h1 : (K / c) ^ 2 ≤ t := by
      have := Nat.le_ceil ((K / c) ^ 2)
      have h2 : ((⌈(K / c) ^ 2⌉₊ : ℕ) : ℝ) ≤ t := by exact_mod_cast le_trans (Nat.le_succ _) ht
      linarith
    calc K / c ≤ |K / c| := le_abs_self _
      _ = Real.sqrt ((K / c) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt t := Real.sqrt_le_sqrt h1
  have hst : Real.sqrt t * Real.sqrt t = t := Real.mul_self_sqrt (by linarith)
  have hA : A ≤ |A| := le_abs_self A
  have hB : B * Real.sqrt t ≤ |B| * Real.sqrt t :=
    mul_le_mul_of_nonneg_right (le_abs_self B) (Real.sqrt_nonneg _)
  have hKs : K ≤ c * Real.sqrt t := by
    have := mul_le_mul_of_nonneg_left hKc hc.le
    rwa [mul_div_cancel₀ K hc.ne'] at this
  calc A + B * Real.sqrt t ≤ |A| * Real.sqrt t + |B| * Real.sqrt t := by
        nlinarith [abs_nonneg A]
    _ = K * Real.sqrt t := by rw [hK]; ring
    _ ≤ (c * Real.sqrt t) * Real.sqrt t :=
        mul_le_mul_of_nonneg_right hKs (Real.sqrt_nonneg _)
    _ = c * t := by rw [mul_assoc, hst]

theorem log_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h := Real.log_le_rpow_div hx (by norm_num : (0 : ℝ) < 1 / 2)
  rw [Real.sqrt_eq_rpow]
  calc Real.log x ≤ x ^ (1 / 2 : ℝ) / (1 / 2) := h
    _ = 2 * x ^ (1 / 2 : ℝ) := by ring

/-- A boundary profile with every multiplicity scaled by `t`. -/
def scaleProfile {ell L : ℕ} (B : Profile ell L) (t : ℕ) : Profile ell (L * t) where
  index := B.index
  index_le := B.index_le
  count s := B.count s * t
  total := by rw [← Finset.sum_mul, B.total]
  supported s h := B.supported s (fun h0 ↦ h (by rw [h0, zero_mul]))

/-- The number of single-grade letters in a scaled profile. -/
theorem scale_ones {ell L : ℕ} (B : Profile ell L) (t : ℕ) :
    (∑ s, (scaleProfile B t).count s * ones s) = t * ∑ s, B.count s * ones s := by
  simp only [scaleProfile, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun s _ ↦ by ring)

/-- `Profile.dim` is the multinomial coefficient times the power of five. -/
theorem dim_eq {ell L : ℕ} (B : Profile ell L) :
    B.dim = Nat.multinomial Finset.univ B.count * 5 ^ (∑ s, B.count s * ones s) := by
  unfold Profile.dim Nat.multinomial
  rw [B.total]

theorem abc_eq {ell L : ℕ} (B : Profile ell L) (z : Fin 3) : B.a z * B.b z * B.c z = B.dim := by
  unfold Profile.a Profile.b Profile.c
  fin_cases z <;> simp

theorem bigAdd_one_iso {K : Type u} [Field K] (M : TensorObj K 3) :
    Isomorphic (bigAdd (fun _ : Fin 1 ↦ M)) M := by
  apply TensorQ.toQ_eq_iff.mp
  rw [TensorQ.toQ_bigAdd, Fin.sum_univ_one]

/-- A finite witness from the exact matrix restriction of a boundary piece. -/
theorem witness_of_dim {K : Type u} [Field K] {ell L : ℕ} (B : Profile ell L) (z : Fin 3)
    (N : ℕ) (tau v : ℝ) (hv : 0 ≤ v)
    (hbound : v ^ N ≤ (B.dim : ℝ) ^ tau) :
    SixFiniteWitness TensorObj.Restrict (B.tensor K z) N tau v := by
  set d := B.a z * B.b z * B.c z with hd
  refine ⟨1, fun _ ↦ d ^ 2, fun _ ↦ d ^ 2, fun _ ↦ d ^ 2, ?_, ?_⟩
  · have hM := mme_recursive_yz_boundary_actual_matrix_extraction (K := K) B z
    have hS := mme_sixSymmetrization_restrict hM
    exact (bigAdd_one_iso _).1.trans
      ((mme_sixSymmetrization_MMObj_isomorphic (B.a z) (B.b z) (B.c z)).2.trans hS)
  · rw [Fin.sum_univ_one, hd, abc_eq]
    have hd0 : (0 : ℝ) ≤ B.dim := Nat.cast_nonneg _
    have hcast : (((B.dim ^ 2 * B.dim ^ 2 * B.dim ^ 2 : ℕ) : ℝ)) = (B.dim : ℝ) ^ (6 : ℕ) := by
      push_cast; ring
    have hpow : ((B.dim : ℝ) ^ (6 : ℕ)) ^ tau = ((B.dim : ℝ) ^ tau) ^ (6 : ℕ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hd0, ← Real.rpow_mul hd0,
        mul_comm]
    rw [hcast, hpow, show 6 * N = N * 6 from mul_comm 6 N, pow_mul]
    exact pow_le_pow_left₀ (pow_nonneg hv N) hbound 6

/-- The entropy-plus-single-letters rate of a boundary profile, per position. -/
noncomputable def rate {ell L : ℕ} (B : Profile ell L) (tau : ℝ) : ℝ :=
  Real.exp (tau * ∑ s, Real.negMulLog ((B.count s : ℝ) / L)) *
    (5 : ℝ) ^ (tau * ((∑ s, B.count s * ones s : ℕ) : ℝ) / L)

theorem card_words : Fintype.card (CompleteWord 2) = 9 := by
  simp [CompleteWord]

/-- The multinomial lower bound in logarithmic form. -/
theorem mult_log_bound {L : ℕ} (B : Profile 2 L) (hL : 0 < L) (t : ℕ) (ht : 0 < t) :
    (t : ℝ) * (L * ∑ s, Real.negMulLog ((B.count s : ℝ) / L)) ≤
      9 * Real.log (6 * (((L * t + 1 : ℕ) : ℝ))) +
        Real.log (Nat.multinomial Finset.univ (fun s ↦ B.count s * t) : ℝ) := by
  have hM := mme_dwz_multinomial_entropy_polynomial_lower B.count t ht
    (by rw [B.total]; exact hL)
  rw [B.total, card_words] at hM
  have hbits : Real.log 2 * mme_modern_entropyBits (fun s ↦ (B.count s : ℝ) / (L : ℝ)) =
      ∑ s, Real.negMulLog ((B.count s : ℝ) / L) := by
    unfold mme_modern_entropyBits
    have : Real.log 2 ≠ 0 := by positivity
    field_simp
  rw [mul_assoc (L : ℝ), hbits] at hM
  have hMpos : (0 : ℝ) < (Nat.multinomial Finset.univ (fun s ↦ B.count s * t) : ℕ) := by
    exact_mod_cast Nat.multinomial_pos _ _
  have hPpos : (0 : ℝ) < 6 * (((L * t + 1 : ℕ) : ℝ)) := by positivity
  have h := Real.log_le_log (Real.exp_pos _) hM
  rwa [Real.log_exp, Real.log_mul (pow_pos hPpos 9).ne' hMpos.ne', Real.log_pow] at h

/-- The polynomial loss is eventually below any linear budget. -/
theorem poly_bound (L : ℕ) (hL : 0 < L) (tau c : ℝ) (htau : 0 ≤ tau) (hc : 0 < c) :
    ∀ᶠ t : ℕ in atTop, 9 * tau * Real.log (6 * (((L * t + 1 : ℕ) : ℝ))) ≤ L * c * t := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  filter_upwards [const_add_sqrt_le 0 (18 * tau * Real.sqrt (12 * L)) (L * c)
      (by positivity), eventually_ge_atTop 1] with t hsq ht
  have htr : (1 : ℝ) ≤ t := by exact_mod_cast ht
  have hPpos : (0 : ℝ) < 6 * (((L * t + 1 : ℕ) : ℝ)) := by positivity
  have hle : 6 * (((L * t + 1 : ℕ) : ℝ)) ≤ 12 * L * t := by
    have h1 : (1 : ℝ) ≤ L := by exact_mod_cast hL
    have h2 : (1 : ℝ) ≤ L * t := by nlinarith
    push_cast
    nlinarith
  have h1 := log_le_two_sqrt hPpos.le
  have h2 : Real.sqrt (6 * (((L * t + 1 : ℕ) : ℝ))) ≤ Real.sqrt (12 * L) * Real.sqrt t := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  have h3 : Real.log (6 * (((L * t + 1 : ℕ) : ℝ))) ≤ 2 * (Real.sqrt (12 * L) * Real.sqrt t) :=
    h1.trans (mul_le_mul_of_nonneg_left h2 (by norm_num))
  have h4 := mul_le_mul_of_nonneg_left h3 (show (0 : ℝ) ≤ 9 * tau by positivity)
  have h5 : 9 * tau * (2 * (Real.sqrt (12 * L) * Real.sqrt t)) =
      18 * tau * Real.sqrt (12 * L) * Real.sqrt t := by ring
  linarith

theorem rate_pos {ell L : ℕ} (B : Profile ell L) (tau : ℝ) : 0 < rate B tau := by
  unfold rate; positivity

theorem log_rate {ell L : ℕ} (B : Profile ell L) (tau : ℝ) :
    Real.log (rate B tau) = tau * (∑ s, Real.negMulLog ((B.count s : ℝ) / L)) +
      tau * ((∑ s, B.count s * ones s : ℕ) : ℝ) / L * Real.log 5 := by
  unfold rate
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity), Real.log_exp,
    Real.log_rpow (by norm_num : (0 : ℝ) < 5)]

theorem scaled_dim {ell L : ℕ} (B : Profile ell L) (t : ℕ) :
    ((scaleProfile B t).dim : ℝ) =
      (Nat.multinomial Finset.univ (fun s ↦ B.count s * t) : ℝ) *
        5 ^ (t * ∑ s, B.count s * ones s) := by
  rw [dim_eq, scale_ones]
  push_cast
  rfl

/-- Along the scaled profiles, the matrix dimension eventually beats every base below `rate`. -/
theorem eventual_bound {L : ℕ} (B : Profile 2 L) (hL : 0 < L) (tau v : ℝ) (htau : 0 ≤ tau)
    (hv : 0 < v) (hvV : v < rate B tau) :
    ∀ᶠ t : ℕ in atTop, v ^ (L * t) ≤ ((scaleProfile B t).dim : ℝ) ^ tau := by
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hcpos : 0 < Real.log (rate B tau) - Real.log v := by
    have := Real.log_lt_log hv hvV
    linarith
  filter_upwards [poly_bound L hL tau _ htau hcpos, eventually_ge_atTop 1] with t hpoly ht
  have hlogM := mult_log_bound B hL t ht
  have hMpos : (0 : ℝ) < (Nat.multinomial Finset.univ (fun s ↦ B.count s * t) : ℕ) := by
    exact_mod_cast Nat.multinomial_pos _ _
  have h5pos : (0 : ℝ) < (5 : ℝ) ^ (t * ∑ s, B.count s * ones s) := by positivity
  have hdimpos : (0 : ℝ) < (scaleProfile B t).dim := by
    rw [scaled_dim]; exact mul_pos hMpos h5pos
  have hlhs : (0 : ℝ) < v ^ (L * t) := pow_pos hv _
  have hrhs : (0 : ℝ) < ((scaleProfile B t).dim : ℝ) ^ tau := Real.rpow_pos_of_pos hdimpos _
  rw [← Real.log_le_log_iff hlhs hrhs, Real.log_pow, Real.log_rpow hdimpos, scaled_dim,
    Real.log_mul hMpos.ne' h5pos.ne', Real.log_pow]
  set H := ∑ s, Real.negMulLog ((B.count s : ℝ) / L)
  set S := ∑ s, B.count s * ones s
  set M := Real.log (Nat.multinomial Finset.univ (fun s ↦ B.count s * t) : ℝ)
  set P := Real.log (6 * (((L * t + 1 : ℕ) : ℝ)))
  have hlogv : Real.log v = tau * H + tau * (S : ℝ) / L * Real.log 5 -
      (Real.log (rate B tau) - Real.log v) := by
    rw [log_rate]; ring
  set c := Real.log (rate B tau) - Real.log v
  rw [hlogv]
  have expand : ((L * t : ℕ) : ℝ) * (tau * H + tau * (S : ℝ) / L * Real.log 5 - c) =
      tau * ((t : ℝ) * (L * H)) + tau * (((t * S : ℕ) : ℝ) * Real.log 5) - L * c * t := by
    push_cast
    field_simp
  have hmul := mul_le_mul_of_nonneg_left hlogM htau
  have hdist : tau * (9 * P + M) = 9 * tau * P + tau * M := by ring
  have hdist2 : tau * (M + ((t * S : ℕ) : ℝ) * Real.log 5) =
      tau * M + tau * (((t * S : ℕ) : ℝ) * Real.log 5) := by ring
  rw [expand, hdist2]
  linarith

/-- Boundary pieces along scaled profiles have eventual witnesses below their rate. -/
theorem boundary_piece_eventual_witness {K : Type u} [Field K] {L : ℕ} (B : Profile 2 L)
    (hL : 0 < L) (z : Fin 3) (tau v : ℝ) (htau : 0 ≤ tau) (hv : 0 < v)
    (hvV : v < rate B tau) :
    ∀ᶠ t : ℕ in atTop,
      SixFiniteWitness TensorObj.Restrict ((scaleProfile B t).tensor K z) (L * t) tau v :=
  (eventual_bound B hL tau v htau hv hvV).mono fun _ ht ↦
    witness_of_dim _ z _ tau v hv.le ht

/-- The matrix dimension depends only on the multiplicities. -/
theorem dim_congr {ell L : ℕ} (B C : Profile ell L) (h : ∀ s, B.count s = C.count s) :
    B.dim = C.dim := by
  unfold Profile.dim
  simp only [h]

end MME.DWZBoundaryValue

open MME.DWZBoundaryValue

theorem solution {K : Type u} [Field K] {L : ℕ}
    (B : Profile 2 L) (hL : 0 < L) (Bt : ∀ t : ℕ, Profile 2 (L * t))
    (hBt : ∀ t s, (Bt t).count s = B.count s * t) (z : Fin 3) (tau v : ℝ)
    (htau : 0 ≤ tau) (hv : 0 < v)
    (hvV : v < Real.exp (tau * ∑ s, Real.negMulLog ((B.count s : ℝ) / L)) *
      (5 : ℝ) ^ (tau * ((∑ s, B.count s * ones s : ℕ) : ℝ) / L)) :
    ∀ᶠ t : ℕ in atTop,
      SixFiniteWitness TensorObj.Restrict ((Bt t).tensor K z) (L * t) tau v := by
  filter_upwards [eventual_bound B hL tau v htau hv hvV] with t ht
  refine witness_of_dim _ z _ tau v hv.le ?_
  rwa [dim_congr (Bt t) (scaleProfile B t) (fun s ↦ hBt t s)]
