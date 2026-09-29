-- Prove2me | solution 2 for rademacher_sampled_matrix_schatten_moment_khintchine_q_ge_two_variance_scale
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-25T03:16:45.883076+00:00
-- url     : https://prove2.me/submissions/45dc9b20-8a83-4397-b004-5a9a2f9308d5

import Definitions.Def_matrix_completion_gram_schatten
import Mathlib.Analysis.InnerProductSpace.SingularValues
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.CompleteLattice.Finset
import Mathlib.Tactic.Positivity
import Theorems.Thm_sum_rpow_le_card_rpow_mul_sum_rpow
import Theorems.Thm_even2n_schatten_moment_bound
import Theorems.Thm_rademacher_expectation_power_mean
import Theorems.Thm_rank_rpow_inv_le_exp_one_of_log_le

open Matrix MatrixCompletion
open scoped BigOperators

/-! ## Helper facts -/

private lemma rExp_nonneg {n1 n2 : Nat} (F : Finset (Fin n1 × Fin n2) → ℝ)
    (hF : ∀ eps, 0 ≤ F eps) : 0 ≤ rademacherExpectation F := by
  unfold rademacherExpectation rademacherObservationWeight
  apply Finset.sum_nonneg
  intro eps _
  apply mul_nonneg (by positivity) (hF eps)

private lemma rExp_mono {n1 n2 : Nat} (F G : Finset (Fin n1 × Fin n2) → ℝ)
    (h : ∀ eps, F eps ≤ G eps) :
    rademacherExpectation F ≤ rademacherExpectation G := by
  unfold rademacherExpectation rademacherObservationWeight
  apply Finset.sum_le_sum
  intro eps _
  apply mul_le_mul_of_nonneg_left (h eps) (by positivity)

private lemma schattenNorm_base_nonneg {n1 n2 : Nat} (q : ℝ) (M : RealMatrix n1 n2) :
    0 ≤ ∑ k : Fin n2, Real.rpow ((Matrix.toEuclideanLin M).singularValues k) q :=
  Finset.sum_nonneg (fun k _ => Real.rpow_nonneg (LinearMap.singularValues_nonneg _ _) _)

private lemma schattenNorm_nonneg {n1 n2 : Nat} (q : ℝ) (M : RealMatrix n1 n2) :
    0 ≤ schattenNorm q M := by
  unfold schattenNorm; exact Real.rpow_nonneg (schattenNorm_base_nonneg q M) _

private lemma schattenNorm_rpow_self {n1 n2 : Nat} (q : ℝ) (hq : 0 < q) (M : RealMatrix n1 n2) :
    (schattenNorm q M) ^ q = ∑ k : Fin n2, ((Matrix.toEuclideanLin M).singularValues k) ^ q := by
  rw [show (schattenNorm q M) ^ q
        = ((∑ k : Fin n2, Real.rpow ((Matrix.toEuclideanLin M).singularValues k) q) ^ (q⁻¹)) ^ q
        from rfl]
  rw [← Real.rpow_mul (schattenNorm_base_nonneg q M)]
  rw [inv_mul_cancel₀ (ne_of_gt hq), Real.rpow_one]
  rfl

/-! ## STEP A (pointwise): schatten_q^q ≤ N^{1-q/2n} · schatten_2n^q -/

private lemma stepA {n1 n2 : Nat} (n : Nat) (hn : 1 ≤ n) (q : ℝ) (hq2 : 2 ≤ q) (hqle : q ≤ 2 * n)
    (M : RealMatrix n1 n2) :
    (schattenNorm q M) ^ q
      ≤ (n2 : ℝ) ^ (1 - q / (2 * n)) * (schattenNorm (2 * n : ℝ) M) ^ q := by
  have hq0 : 0 < q := by linarith
  have h2n0 : (0:ℝ) < 2 * n := by positivity
  set σ : Fin n2 → ℝ := fun k => (Matrix.toEuclideanLin M).singularValues k with hσdef
  have hσ0 : ∀ k, 0 ≤ σ k := fun k => LinearMap.singularValues_nonneg _ _
  rw [schattenNorm_rpow_self q hq0 M]
  have hpm := sum_rpow_le_card_rpow_mul_sum_rpow σ hσ0 q (2 * n : ℝ) hq0 hqle
  have hb : (∑ k, (σ k) ^ (2 * n : ℝ)) ^ (q / (2 * n)) = (schattenNorm (2 * n : ℝ) M) ^ q := by
    rw [← schattenNorm_rpow_self (2 * n : ℝ) h2n0 M]
    rw [← Real.rpow_mul (schattenNorm_nonneg _ _)]
    congr 1
    field_simp
  rw [hb] at hpm
  exact hpm

/-! ## Window collapse: N^{1-q/2n} ≤ e²  -/

private lemma window_collapse (N : ℕ) (hN : 1 ≤ N) (n : ℕ) (hn : 1 ≤ n) (q : ℝ)
    (hq2 : 2 ≤ q) (hqle : q ≤ 2 * n) (h2nle : (2 * n : ℝ) ≤ q + 2)
    (hlogN : Real.log (N : ℝ) ≤ q) :
    (N : ℝ) ^ (1 - q / (2 * n)) ≤ Real.exp 1 ^ 2 := by
  have hq0 : 0 < q := by linarith
  have h2n0 : (0:ℝ) < 2 * n := by positivity
  have hN1 : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0:ℝ) < N := by linarith
  have hexp : 1 - q / (2 * n) ≤ 2 / q := by
    have hstep1 : 1 - q / (2 * n) ≤ 2 / (2 * n) := by
      have h1 : (1 - q / (2 * n)) = ((2 * n : ℝ) - q) / (2 * n) := by field_simp
      rw [h1, div_le_div_iff_of_pos_right h2n0]
      linarith
    have hstep2 : 2 / (2 * n : ℝ) ≤ 2 / q := by
      apply div_le_div_of_nonneg_left (by norm_num) hq0 hqle
    linarith
  calc (N : ℝ) ^ (1 - q / (2 * n))
      ≤ (N : ℝ) ^ (2 / q) := by
        apply Real.rpow_le_rpow_of_exponent_le hN1 hexp
    _ = ((N : ℝ) ^ (q⁻¹)) ^ (2:ℝ) := by
        rw [← Real.rpow_mul (le_of_lt hNpos)]
        congr 1; rw [inv_mul_eq_div]
    _ ≤ (Real.exp 1) ^ (2:ℝ) := by
        apply Real.rpow_le_rpow (Real.rpow_nonneg (le_of_lt hNpos) _)
        · exact rank_rpow_inv_le_exp_one_of_log_le N q hN (by linarith) hlogN
        · norm_num
    _ = Real.exp 1 ^ 2 := by rw [show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, Real.rpow_natCast]

/-! ## Combined general-q bound -/

private lemma general_q_bound {n1 n2 : Nat} (n : Nat) (hn : 1 ≤ n)
    (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : 0 ≤ p) (X : RealMatrix n1 n2)
    (q : ℝ) (hq2 : 2 ≤ q) (hqle : q ≤ 2 * n) (h2nle : (2 * n : ℝ) ≤ q + 2)
    (hd1 : 1 ≤ (n1 + n2)) (hlogd : Real.log ((n1 + n2 : ℕ)) ≤ (2 * n : ℕ))
    (hN1 : 1 ≤ n2) (hlogN : Real.log (n2 : ℝ) ≤ q) :
    rademacherExpectation (fun eps =>
        schattenNorm q (rademacherSampledMatrix Omega eps p X) ^ q)
      ≤ Real.exp 1 ^ 2 *
          (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rademacherSampledVarianceScale Omega p X) ^ q := by
  have hq0 : 0 < q := by linarith
  have h2n0 : (0:ℝ) < 2 * n := by positivity
  set rsvs := rademacherSampledVarianceScale Omega p X with hrsvs
  set G : Finset (Fin n1 × Fin n2) → ℝ :=
    fun eps => schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) with hG
  have hGnn : ∀ eps, 0 ≤ G eps := fun eps => schattenNorm_nonneg _ _
  have hB : rademacherExpectation (fun eps =>
              schattenNorm q (rademacherSampledMatrix Omega eps p X) ^ q)
            ≤ (n2 : ℝ) ^ (1 - q / (2 * n)) *
                rademacherExpectation (fun eps => (G eps) ^ q) := by
    rw [show (n2 : ℝ) ^ (1 - q / (2 * n)) * rademacherExpectation (fun eps => (G eps) ^ q)
          = rademacherExpectation (fun eps => (n2 : ℝ) ^ (1 - q / (2 * n)) * (G eps) ^ q) from ?_]
    · apply rExp_mono
      intro eps
      exact stepA n hn q hq2 hqle (rademacherSampledMatrix Omega eps p X)
    · unfold rademacherExpectation
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro eps _; ring
  have hJ := rademacher_expectation_power_mean (n1 := n1) (n2 := n2) q (2 * n) hq0 hqle G hGnn
  have hD : rademacherExpectation (fun eps => (G eps) ^ (2 * n : ℝ))
            ≤ (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs) ^ (2 * n) := by
    have := even2n_schatten_moment_bound n hn Omega p X hd1 hlogd
    have halign : (fun eps => (G eps) ^ (2 * n : ℝ))
        = (fun eps => schattenNorm (2 * n : ℝ) (rademacherSampledMatrix Omega eps p X) ^ (2 * n)) := by
      funext eps
      rw [hG]
      rw [← Real.rpow_natCast (schattenNorm (2*n:ℝ) (rademacherSampledMatrix Omega eps p X)) (2*n)]
      norm_num
    rw [halign]
    exact this
  have hExpGq_nn : 0 ≤ rademacherExpectation (fun eps => (G eps) ^ (2 * n : ℝ)) :=
    rExp_nonneg _ (fun eps => Real.rpow_nonneg (hGnn eps) _)
  have hrsvs_nn : 0 ≤ rsvs := by
    rw [hrsvs]; unfold rademacherSampledVarianceScale
    apply mul_nonneg (inv_nonneg.mpr hp) (Real.sqrt_nonneg _)
  have hRHS_nn : 0 ≤ Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs := by
    apply mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) (le_of_lt (Real.exp_pos _))) hrsvs_nn
  have hChain : rademacherExpectation (fun eps => (G eps) ^ q)
      ≤ (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs) ^ q := by
    calc rademacherExpectation (fun eps => (G eps) ^ q)
        ≤ (rademacherExpectation (fun eps => (G eps) ^ (2 * n : ℝ))) ^ (q / (2 * n)) := hJ
      _ ≤ ((Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs) ^ (2 * n)) ^ (q / (2 * n)) := by
            apply Real.rpow_le_rpow hExpGq_nn hD (by positivity)
      _ = (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs) ^ q := by
            rw [← Real.rpow_natCast (Real.sqrt (2*n:ℕ) * Real.exp 1 * rsvs) (2*n)]
            rw [← Real.rpow_mul hRHS_nn]
            congr 1; push_cast; field_simp
  have hwin := window_collapse n2 hN1 n hn q hq2 hqle h2nle hlogN
  calc rademacherExpectation (fun eps =>
          schattenNorm q (rademacherSampledMatrix Omega eps p X) ^ q)
      ≤ (n2 : ℝ) ^ (1 - q / (2 * n)) * rademacherExpectation (fun eps => (G eps) ^ q) := hB
    _ ≤ Real.exp 1 ^ 2 * (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs) ^ q := by
        apply mul_le_mul hwin hChain
          (rExp_nonneg _ (fun eps => Real.rpow_nonneg (hGnn eps) _))
        positivity

/-! ## Constant fold -/

private lemma const_fold (n : ℕ) (hn : 1 ≤ n) (q : ℝ) (hq2 : 2 ≤ q) (h2nle : (2 * n : ℝ) ≤ q + 2)
    (rsvs : ℝ) (hrsvs : 0 ≤ rsvs) :
    Real.exp 1 ^ 2 * (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs) ^ q
      ≤ ((Real.exp 1 ^ 3 * Real.sqrt 2) * Real.sqrt q * rsvs) ^ q := by
  have hq0 : 0 < q := by linarith
  have he1 : (1:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
  have hepos : 0 < Real.exp 1 := Real.exp_pos _
  have h2n2q : (2 * n : ℝ) ≤ 2 * q := by nlinarith
  have hsqrt : Real.sqrt (2 * n : ℕ) ≤ Real.sqrt 2 * Real.sqrt q := by
    rw [← Real.sqrt_mul (by norm_num)]
    apply Real.sqrt_le_sqrt
    push_cast; linarith
  set A : ℝ := Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs with hAdef
  set Bc : ℝ := (Real.exp 1 ^ 3 * Real.sqrt 2) * Real.sqrt q * rsvs with hBdef
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hkey : Real.exp 1 ^ 2 * A ≤ Bc := by
    rw [hAdef, hBdef]
    have hstep : Real.exp 1 ^ 2 * (Real.sqrt (2 * n : ℕ) * Real.exp 1)
        ≤ Real.exp 1 ^ 3 * Real.sqrt 2 * Real.sqrt q := by
      have hsq2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
      have hsqq : 0 ≤ Real.sqrt q := Real.sqrt_nonneg _
      calc Real.exp 1 ^ 2 * (Real.sqrt (2 * n : ℕ) * Real.exp 1)
          = Real.exp 1 ^ 3 * Real.sqrt (2 * n : ℕ) := by ring
        _ ≤ Real.exp 1 ^ 3 * (Real.sqrt 2 * Real.sqrt q) := by
            apply mul_le_mul_of_nonneg_left hsqrt (by positivity)
        _ = Real.exp 1 ^ 3 * Real.sqrt 2 * Real.sqrt q := by ring
    calc Real.exp 1 ^ 2 * (Real.sqrt (2 * n : ℕ) * Real.exp 1 * rsvs)
        = (Real.exp 1 ^ 2 * (Real.sqrt (2 * n : ℕ) * Real.exp 1)) * rsvs := by ring
      _ ≤ (Real.exp 1 ^ 3 * Real.sqrt 2 * Real.sqrt q) * rsvs := by
          apply mul_le_mul_of_nonneg_right hstep hrsvs
      _ = Real.exp 1 ^ 3 * Real.sqrt 2 * Real.sqrt q * rsvs := by ring
  have hB0 : 0 ≤ Bc := le_trans (by positivity) hkey
  have hstep1 : Real.exp 1 ^ 2 * A ^ q ≤ (Real.exp 1 ^ 2 * A) ^ q := by
    rw [Real.mul_rpow (by positivity) hA0]
    apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hA0 q)
    have hbase1 : (1:ℝ) ≤ Real.exp 1 ^ 2 := by nlinarith [hepos, he1]
    calc Real.exp 1 ^ 2 = (Real.exp 1 ^ 2) ^ (1:ℝ) := by rw [Real.rpow_one]
      _ ≤ (Real.exp 1 ^ 2) ^ q := Real.rpow_le_rpow_of_exponent_le hbase1 (by linarith)
  calc Real.exp 1 ^ 2 * A ^ q
      ≤ (Real.exp 1 ^ 2 * A) ^ q := hstep1
    _ ≤ Bc ^ q := by apply Real.rpow_le_rpow (by positivity) hkey (le_of_lt hq0)

/-! ## FINAL : the exact 3090c7ef target -/

theorem solution :
    ∃ Ckh : ℝ, 0 < Ckh ∧
      ∀ C' : ℝ, Ckh ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m q : ℕ)
        (Omega : Finset (Fin n₁ × Fin n₂))
        (X : Matrix (Fin n₁) (Fin n₂) ℝ),
        2 ≤ q →
        (q : ℝ) ≥ β * Real.log (↑(max n₁ n₂)) →
        rademacherExpectation
            (fun eps =>
              schattenNorm (q : ℝ)
                (rademacherSampledMatrix Omega eps
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q) ≤
          (C' * Real.sqrt (q : ℝ) *
            rademacherSampledVarianceScale Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) X) ^ q := by
  refine ⟨Real.exp 1 ^ 3 * Real.sqrt 2, by positivity, ?_⟩
  intro C' hC' β hβ n₁ n₂ m q Omega X hq2 hqlog
  rw [Nat.cast_max] at hqlog
  set p : ℝ := (m:ℝ)/((n₁:ℝ)*(n₂:ℝ)) with hp
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  set rsvs := rademacherSampledVarianceScale Omega p X with hrsvs
  have hrsvs0 : 0 ≤ rsvs := by
    rw [hrsvs]; unfold rademacherSampledVarianceScale; positivity
  rcases Nat.eq_zero_or_pos n₂ with hn2z | hN1
  · subst hn2z
    have hLHS0 : rademacherExpectation (fun eps =>
        schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X) ^ q) = 0 := by
      have hsch0 : ∀ eps : Finset (Fin n₁ × Fin 0),
          schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X) = 0 := by
        intro eps
        unfold schattenNorm
        rw [Finset.sum_of_isEmpty]
        exact Real.zero_rpow (by positivity)
      have : (fun eps => schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X) ^ q)
          = (fun _ : Finset (Fin n₁ × Fin 0) => (0:ℝ)) := by
        funext eps; rw [hsch0 eps]; exact zero_pow (by omega)
      rw [this]
      unfold rademacherExpectation
      simp
    rw [hLHS0]
    have hC'0 : 0 ≤ C' := le_trans (by positivity) hC'
    apply pow_nonneg
    apply mul_nonneg (mul_nonneg hC'0 (Real.sqrt_nonneg _)) hrsvs0
  set n : ℕ := (q + 1) / 2 with hndef
  have hqR : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq2
  have hn1 : 1 ≤ n := by rw [hndef]; omega
  have h2n_ge : q ≤ 2 * n := by rw [hndef]; omega
  have h2n_le : 2 * n ≤ q + 1 := by rw [hndef]; omega
  have hqle : (q:ℝ) ≤ (2 * n : ℝ) := by exact_mod_cast h2n_ge
  have h2nle : (2 * n : ℝ) ≤ (q:ℝ) + 2 := by
    have : (2 * n : ℝ) ≤ (q:ℝ) + 1 := by exact_mod_cast h2n_le
    linarith
  have hmaxpos : (1:ℝ) ≤ (max n₁ n₂ : ℝ) := by
    have hnat : 1 ≤ max n₁ n₂ := le_trans hN1 (le_max_right n₁ n₂)
    have : (1:ℝ) ≤ ((max n₁ n₂ : ℕ) : ℝ) := by exact_mod_cast hnat
    rwa [Nat.cast_max] at this
  have hlogmax_nn : 0 ≤ Real.log (max n₁ n₂ : ℝ) := Real.log_nonneg hmaxpos
  have hq_ge_2logmax : (q:ℝ) ≥ 2 * Real.log (max n₁ n₂ : ℝ) := by
    have : β * Real.log (max n₁ n₂ : ℝ) ≥ 2 * Real.log (max n₁ n₂ : ℝ) := by
      apply mul_le_mul_of_nonneg_right (le_of_lt hβ) hlogmax_nn
    linarith
  have hlogN : Real.log (n₂ : ℝ) ≤ (q:ℝ) := by
    have h1 : Real.log (n₂ : ℝ) ≤ Real.log (max n₁ n₂ : ℝ) := by
      rcases Nat.eq_zero_or_pos n₂ with h0 | hpos
      · simp [h0]; positivity
      · apply Real.log_le_log (by exact_mod_cast hpos)
        exact_mod_cast le_max_right n₁ n₂
    have h2 : Real.log (max n₁ n₂ : ℝ) ≤ (q:ℝ) := by
      nlinarith [hlogmax_nn]
    linarith
  have hd1 : 1 ≤ n₁ + n₂ := by omega
  have hlogd : Real.log ((n₁ + n₂ : ℕ)) ≤ ((2 * n : ℕ):ℝ) := by
    have hsum_le : ((n₁ + n₂ : ℕ):ℝ) ≤ 2 * (max n₁ n₂ : ℝ) := by
      push_cast; rw [two_mul]
      have ha : (n₁ : ℝ) ≤ (max n₁ n₂ : ℝ) := by exact_mod_cast le_max_left n₁ n₂
      have hb : (n₂ : ℝ) ≤ (max n₁ n₂ : ℝ) := by exact_mod_cast le_max_right n₁ n₂
      linarith
    have hsumpos : (0:ℝ) < ((n₁ + n₂ : ℕ):ℝ) := by exact_mod_cast hd1
    calc Real.log ((n₁ + n₂ : ℕ):ℝ)
        ≤ Real.log (2 * (max n₁ n₂ : ℝ)) := Real.log_le_log hsumpos hsum_le
      _ = Real.log 2 + Real.log (max n₁ n₂ : ℝ) := by
          rw [Real.log_mul (by norm_num) (by positivity)]
      _ ≤ (q:ℝ) := by
          have hlog2le1 : Real.log 2 ≤ 1 := by
            rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
            apply Real.log_le_log (by norm_num)
            linarith [Real.add_one_le_exp (1:ℝ)]
          linarith [hlog2le1, hq_ge_2logmax, hqR]
      _ ≤ ((2 * n : ℕ):ℝ) := by exact_mod_cast h2n_ge
  have hgen := general_q_bound n hn1 Omega p hp0 X (q:ℝ) hqR hqle h2nle hd1 hlogd hN1 hlogN
  have hcf := const_fold n hn1 (q:ℝ) hqR h2nle rsvs hrsvs0
  have hcombined : rademacherExpectation (fun eps =>
        schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X) ^ (q:ℝ))
      ≤ ((Real.exp 1 ^ 3 * Real.sqrt 2) * Real.sqrt (q:ℝ) * rsvs) ^ (q:ℝ) :=
    le_trans hgen hcf
  have hq0 : (0:ℝ) < (q:ℝ) := by linarith [hqR]
  have hLHS_eq : rademacherExpectation (fun eps =>
        schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X) ^ q)
      = rademacherExpectation (fun eps =>
        schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X) ^ (q:ℝ)) := by
    apply congrArg
    funext eps
    rw [← Real.rpow_natCast (schattenNorm (q:ℝ) (rademacherSampledMatrix Omega eps p X)) q]
  rw [hLHS_eq]
  have hCkh_le : (Real.exp 1 ^ 3 * Real.sqrt 2) ≤ C' := hC'
  have hbase_nn : 0 ≤ C' * Real.sqrt (q:ℝ) * rsvs := by
    have : 0 ≤ C' := le_trans (by positivity) hC'
    apply mul_nonneg (mul_nonneg this (Real.sqrt_nonneg _)) hrsvs0
  rw [← Real.rpow_natCast (C' * Real.sqrt (q:ℝ) * rsvs) q]
  refine le_trans hcombined ?_
  apply Real.rpow_le_rpow (by positivity) ?_ (le_of_lt hq0)
  apply mul_le_mul_of_nonneg_right _ hrsvs0
  apply mul_le_mul_of_nonneg_right hCkh_le (Real.sqrt_nonneg _)

#print axioms solution
