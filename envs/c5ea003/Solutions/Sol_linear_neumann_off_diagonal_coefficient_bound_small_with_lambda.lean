-- Prove2me | solution 1 for linear_neumann_off_diagonal_coefficient_bound_small_with_lambda
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T21:16:55.886864+00:00
-- url     : https://prove2.me/submissions/c265fca8-5e11-45a4-b1f9-b59600f62a6b

import Definitions.Def_matrix_completion_basic
import Definitions.Def_linear_neumann_offdiag_bernstein
import Mathlib.Data.Fintype.Order
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
import Definitions.Def_matrix_completion_svd
import Mathlib
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_min_dim_base_bounds
import Theorems.Thm_linear_neumann_off_diagonal_coefficient_entry_as_centered_scalar_fluctuation

/- Two complete accepted-source bodies with explicit import, namespace, and final-name transformations: ReusedSampling.lean; SHA256 b65317d57659402837ffc8df68a62d3a663cd64f0a33dced67d5fcf37afa019d. -/

/- Complete accepted-source reuse: theorem c0188309-6fd2-4977-a823-31e1aa3eee1e; submission 84cc520d-97f3-4fbd-aaac-6e2b0d917c75.
Original SHA256 252cf2cbbd05955213f7b0ab6692097206d78d70ce0aba02135568ef6a353c30. All proof/helper bodies retained.
Imports consolidated explicitly; affected public imports replaced by the complete local bodies.
Only the final declaration name changes from solution to sample_ratio_between_zero_and_one.
A unique namespace under MatrixCompletion prevents private helper collisions and norm-name ambiguity. -/
namespace MatrixCompletion.MatrixCoefficientReuse_c0188309

open MatrixCompletion

theorem sample_ratio_between_zero_and_one
    (n₁ n₂ m : ℕ) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
    0 ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ∧
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ≤ 1 := by
  intro hn₁ hn₂ hm
  constructor
  · exact div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have hden_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) := by
      exact mul_pos (Nat.cast_pos.mpr hn₁) (Nat.cast_pos.mpr hn₂)
    have hnum_le_den : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
      exact_mod_cast hm
    rw [div_le_iff₀ hden_pos]
    simpa using hnum_le_den


end MatrixCompletion.MatrixCoefficientReuse_c0188309
export MatrixCompletion.MatrixCoefficientReuse_c0188309 (sample_ratio_between_zero_and_one)

/- Complete accepted-source reuse: theorem 77578034-444f-4e3c-a1b1-985fb5cc3237; submission fcaaf54e-c686-4001-9667-be0f895c7796.
Original SHA256 1dbb1ac9ca370ad8b8c2997b5d194f775e639c1c6225bc6a36f41301e488e27d. All proof/helper bodies retained.
Imports consolidated explicitly; affected public imports replaced by the complete local bodies.
Only the final declaration name changes from solution to linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_min_dim_shifted_pointwise_tails.
A unique namespace under MatrixCompletion prevents private helper collisions and norm-name ambiguity. -/
namespace MatrixCompletion.MatrixCoefficientReuse_77578034

open MatrixCompletion

open MatrixCompletion

/-!
Source: Candès--Recht 2008, Section 6.2, Lemma 6.6, equations
(6.15)--(6.17), and the union bound immediately after (6.17).
-/

private lemma entrySupNorm_le_of_forall_abs_le {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (B : ℝ)
    (h : ∀ w : Fin n₁ × Fin n₂, |X w.1 w.2| ≤ B) :
    entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => h (i, j)

theorem linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_min_dim_shifted_pointwise_tails
    (Cpoint cpoint Centry Cfro : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∃ Ctwo ctwo : ℝ, 0 < Ctwo ∧ 0 < ctwo ∧
      ∀ C' : ℝ,
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        (∀ w : Fin n₁ × Fin n₂,
          bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega2 =>
                |linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) w.1 w.2| ≤
                  Cpoint *
                    (Real.sqrt
                        (((β + 2) * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (Cfro * μ₁ *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                      (((β + 2) * Real.log (↑(max n₁ n₂))) /
                          ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                        (Centry * μ₁ *
                          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                            (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))))) ≥
            1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ctwo *
                  (Real.sqrt
                      (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    (Cfro * μ₁ *
                      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                    (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (Centry * μ₁ *
                        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                          (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))))) ≥
          1 - ctwo * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro hCpoint hcpoint
  rcases bernoulli_uniform_bound_over_matrix_indices_from_shifted_pointwise_tails
      Cpoint cpoint hCpoint hcpoint with
    ⟨Ctwo, ctwo, hCtwo, hctwo, hUniform⟩
  refine ⟨Ctwo, ctwo, hCtwo, hctwo, ?_⟩
  intro C' β hβ n₁ n₂ r m M μ₀ μ₁ S
    hn₁ hn₂ _hr hm _hμ₀ _hμ₁ _hA0 _hA1 _hmLower hPointwise
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hp_nonneg, hp_le_one⟩
  let p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))
  let twoTermScale : ℝ :=
    Real.sqrt
        (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
      (Cfro * μ₁ *
        Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
          Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
      (((β + 2) * Real.log (↑(max n₁ n₂))) / p) *
        (Centry * μ₁ *
          Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
            (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))
  have hPointwise' :
      ∀ w : Fin n₁ × Fin n₂,
        bernoulliEventProb p
            (fun Omega2 =>
              |linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                  p w.1 w.2| ≤
                Cpoint * twoTermScale) ≥
          1 - cpoint * Real.rpow (↑(max n₁ n₂)) (-(β + 2)) := by
    intro w
    simpa [p, twoTermScale, mul_assoc] using hPointwise w
  have hUniformEvent :
      bernoulliEventProb p
          (fun Omega2 =>
            ∀ w : Fin n₁ × Fin n₂,
              |linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                  p w.1 w.2| ≤
                Ctwo * twoTermScale) ≥
        1 - ctwo * Real.rpow (↑(max n₁ n₂)) (-β) :=
    hUniform β p twoTermScale hβ hp_nonneg hp_le_one n₁ n₂ hn₁ hn₂
      (fun w Omega2 =>
        linearNeumannOffDiagonalCoefficientMatrix Omega2 S p w.1 w.2)
      hPointwise'
  have hMono :
      bernoulliEventProb p
          (fun Omega2 =>
            ∀ w : Fin n₁ × Fin n₂,
              |linearNeumannOffDiagonalCoefficientMatrix Omega2 S
                  p w.1 w.2| ≤
                Ctwo * twoTermScale) ≤
        bernoulliEventProb p
          (fun Omega2 =>
            LinearNeumannOffDiagonalCoefficientBound Omega2 S p
              (Ctwo * twoTermScale)) := by
    refine bernoulli_event_probability_mono p _ _ hp_nonneg hp_le_one ?_
    intro Omega2 hAll
    exact entrySupNorm_le_of_forall_abs_le hn₁ hn₂
      (linearNeumannOffDiagonalCoefficientMatrix Omega2 S p)
      (Ctwo * twoTermScale) hAll
  simpa [p, twoTermScale, mul_assoc] using le_trans hUniformEvent hMono


end MatrixCompletion.MatrixCoefficientReuse_77578034
export MatrixCompletion.MatrixCoefficientReuse_77578034 (linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_min_dim_shifted_pointwise_tails)


/- Complete unchanged Round42 accepted component: SvdLeverage.lean; SHA256 d0afce6765032f7a3970d12f85ee70eb24ab340c4342e5b77b7cae363bae3546. -/

namespace MatrixThreshold

open MatrixCompletion
open scoped BigOperators

theorem sum_sq_orthonormal_combination {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (c : I -> Real) (v : I -> J -> Real)
    (hv : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0) :
    ∑ j, (∑ k, c k * v k j) ^ 2 = ∑ k, c k ^ 2 := by
  classical
  calc
    _ = ∑ k, ∑ l, c k * c l * (∑ j, v k j * v l j) := by
      simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro l hl
      apply Finset.sum_congr rfl
      intro j hj
      ring
    _ = _ := by simp [hv, pow_two]

theorem orthonormal_leverage_le_one {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] (v : I -> J -> Real)
    (hv : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0) (i : J) :
    ∑ k, (v k i) ^ 2 <= 1 := by
  classical
  have h := sum_sq_orthonormal_combination (fun k => v k i) v hv
  have hle := Finset.single_le_sum
    (fun j (_ : j ∈ Finset.univ) => sq_nonneg (∑ k, v k i * v k j))
    (Finset.mem_univ i)
  rw [h] at hle
  simp only [← pow_two] at hle
  nlinarith [sq_nonneg ((∑ k, (v k i) ^ 2) - 1)]

theorem sign_row_sq_sum_eq_leverage {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (i : Fin n1) :
    ∑ j, (signMatrix S i j) ^ 2 = ∑ k, (S.u k i) ^ 2 := by
  simpa [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply] using
    sum_sq_orthonormal_combination (fun k => S.u k i) S.v S.v_orthonormal

theorem sign_column_sq_sum_eq_leverage {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (j : Fin n2) :
    ∑ i, (signMatrix S i j) ^ 2 = ∑ k, (S.v k j) ^ 2 := by
  simpa [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply, mul_comm] using
    sum_sq_orthonormal_combination (fun k => S.v k j) S.u S.u_orthonormal

theorem row_leverage_le_one {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (i : Fin n1) : ∑ k, (S.u k i) ^ 2 <= 1 :=
  orthonormal_leverage_le_one S.u S.u_orthonormal i

theorem column_leverage_le_one {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (j : Fin n2) : ∑ k, (S.v k j) ^ 2 <= 1 :=
  orthonormal_leverage_le_one S.v S.v_orthonormal j

theorem sign_sq_le_of_A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu : Real) (hmu : 0 <= mu) (hA1 : A1 S mu)
    (i : Fin n1) (j : Fin n2) :
    (signMatrix S i j) ^ 2 <= mu ^ 2 * (r : Real) / ((n1 : Real) * (n2 : Real)) := by
  have h := sq_le_sq₀ (abs_nonneg (signMatrix S i j))
    (mul_nonneg hmu (Real.sqrt_nonneg ((r : Real) / ((n1 : Real) * (n2 : Real)))))
  have hs := h.mpr (hA1 i j)
  rw [sq_abs, mul_pow, Real.sq_sqrt (by positivity)] at hs
  convert hs using 1
  ring

theorem row_leverage_le_of_A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu : Real) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hmu : 0 <= mu) (hA1 : A1 S mu) (i : Fin n1) :
    ∑ k, (S.u k i) ^ 2 <= mu ^ 2 * (r : Real) / (n1 : Real) := by
  rw [← sign_row_sq_sum_eq_leverage S i]
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
    sign_sq_le_of_A1 S mu hmu hA1 i j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  convert h using 1
  field_simp

theorem column_leverage_le_of_A1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu : Real) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hmu : 0 <= mu) (hA1 : A1 S mu) (j : Fin n2) :
    ∑ k, (S.v k j) ^ 2 <= mu ^ 2 * (r : Real) / (n2 : Real) := by
  rw [← sign_column_sq_sum_eq_leverage S j]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    sign_sq_le_of_A1 S mu hmu hA1 i j)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  convert h using 1
  field_simp

end MatrixThreshold

/- Complete unchanged root-authored scalar absorption component: ScalarAbsorption.lean; SHA256 f9e33815fd927603e692d7eda7f9f2d04009e26cdee5dba1722987765368383e. -/

namespace MatrixOffdiag

lemma scalar_absorption (q z w Bf Be : ℝ)
    (hq : q ≤ 2) (hz : 0 ≤ z) (hz1 : z ≤ 1) (hzw : z ≤ w)
    (hBf : 0 ≤ Bf) (hBe : 0 ≤ Be) :
    Real.sqrt (q * z) * Bf + (q * z) * Be ≤
      2 * (Bf + Be) * Real.sqrt w := by
  have hzs : z ≤ Real.sqrt z := by
    have := mul_nonneg hz (sub_nonneg.mpr hz1)
    nlinarith [Real.sq_sqrt hz, Real.sqrt_nonneg z]
  have hs : Real.sqrt (q * z) ≤ 2 * Real.sqrt z := by
    calc
      _ ≤ Real.sqrt (4 * z) := Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_right (le_trans hq (by norm_num)) hz)
      _ = _ := by rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]; norm_num
  have hl : q * z ≤ 2 * Real.sqrt z :=
    (mul_le_mul_of_nonneg_right hq hz).trans
      (mul_le_mul_of_nonneg_left hzs (by norm_num))
  calc
    _ ≤ (2 * Real.sqrt z) * Bf + (2 * Real.sqrt z) * Be :=
      add_le_add (mul_le_mul_of_nonneg_right hs hBf) (mul_le_mul_of_nonneg_right hl hBe)
    _ = 2 * (Bf + Be) * Real.sqrt z := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hzw) (by positivity)

end MatrixOffdiag

/- New A1-to-A0 effective coherence reduction: EffectiveCoherence.lean; SHA256 95cff2ff74dffdfef1f73dd9cfd997347df9ebb913b93e4bda156f5abc677688. -/

namespace MatrixOffdiag

open MatrixCompletion
open scoped BigOperators

theorem coherence_le_of_leverage {N r : Nat} (v : Fin r -> Fin N -> Real)
    (hN : 0 < N) (hr : 0 < r) (mu : Real)
    (h : ∀ i, ∑ k, (v k i) ^ 2 <= mu * (r : Real) / (N : Real)) :
    coherence N r v <= mu := by
  haveI : Nonempty (Fin N) := Fin.pos_iff_nonempty.mp hN
  have hN' : (0 : Real) < N := by exact_mod_cast hN
  have hr' : (0 : Real) < r := by exact_mod_cast hr
  unfold coherence
  calc
    _ <= (N : Real) / r * (mu * r / N) :=
      mul_le_mul_of_nonneg_left (ciSup_le h) (by positivity)
    _ = mu := by field_simp

theorem a0_of_a1 {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu : Real) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hr : 0 < r) (hmu : 0 <= mu) (hA1 : A1 S mu) : A0 S (mu ^ 2) := by
  constructor
  · exact coherence_le_of_leverage S.u hn1 hr (mu ^ 2)
      (MatrixThreshold.row_leverage_le_of_A1 S mu hn1 hn2 hmu hA1)
  · exact coherence_le_of_leverage S.v hn2 hr (mu ^ 2)
      (MatrixThreshold.column_leverage_le_of_A1 S mu hn1 hn2 hmu hA1)

theorem a0_min {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (a b : Real) (ha : A0 S a) (hb : A0 S b) :
    A0 S (min a b) :=
  ⟨le_min ha.1 hb.1, le_min ha.2 hb.2⟩

theorem effective_coherence {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (mu0 mu1 : Real) (hn1 : 0 < n1) (hn2 : 0 < n2)
    (hr : 0 < r) (hmu0 : 1 <= mu0) (hmu1 : 1 <= mu1)
    (hA0 : A0 S mu0) (hA1 : A1 S mu1) :
    1 <= min mu0 (mu1 ^ 2) ∧ A0 S (min mu0 (mu1 ^ 2)) := by
  refine ⟨le_min hmu0 (by nlinarith), ?_⟩
  exact a0_min S _ _ hA0
    (a0_of_a1 S mu1 hn1 hn2 hr (by linarith) hA1)

end MatrixOffdiag

/- New exact raw Bernstein threshold normalization and absorption: RawThreshold.lean; SHA256 3cb50ba67b205294bd2761f9de8edec6865b88da85fb3268f77ee66b07c06232. -/

namespace MatrixOffdiag

theorem density_le_of_sample (lam mu0 mu1 a n r L m : Real)
    (hlam : 1 <= lam) (hmu1 : 0 <= mu1) (ha : a <= mu1 ^ 2)
    (hn : 0 <= n) (hr : 0 <= r) (hL : 0 <= L)
    (hm : lam * mu1 * max (Real.sqrt mu0) mu1 * n * r * L <= m) :
    a * n * r * L <= m := by
  have hmax : mu1 <= max (Real.sqrt mu0) mu1 := le_max_right _ _
  have hmax0 : 0 <= max (Real.sqrt mu0) mu1 := hmu1.trans hmax
  have hcoef : a <= lam * mu1 * max (Real.sqrt mu0) mu1 := by
    calc
      a <= mu1 ^ 2 := ha
      _ <= mu1 * max (Real.sqrt mu0) mu1 := by
        nlinarith [mul_nonneg hmu1 (sub_nonneg.mpr hmax)]
      _ <= lam * (mu1 * max (Real.sqrt mu0) mu1) := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hlam) (mul_nonneg hmu1 hmax0)]
      _ = _ := by ring
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hcoef hn) hr) hL).trans hm

theorem raw_threshold_le (Bf Be E C a mu0 n s r m beta L : Real)
    (hBf : 0 <= Bf) (hBe : 0 <= Be) (hE : 0 <= E) (hC : 0 <= C)
    (ha0 : 0 <= a) (ha : a <= mu0) (hn : 0 < n) (hs : 0 < s)
    (hr : 0 <= r) (hm : 0 <= m) (hbeta : 2 < beta) (hL : 0 <= L)
    (hdensity : a * n * r * (beta * L) <= m) :
    C * (Real.sqrt (((beta + 2) * L) / (m / (n * s))) *
        (Bf * E * Real.sqrt (a * r / s)) +
      (((beta + 2) * L) / (m / (n * s))) * (Be * E * (a * r / s))) <=
      (2 * C * (Bf + Be)) * E * Real.sqrt (mu0 * n * r * (beta * L) / m) := by
  by_cases hm0 : m = 0
  · simp [hm0]
  have hmpos : 0 < m := lt_of_le_of_ne hm (Ne.symm hm0)
  have hbeta0 : 0 < beta := by linarith
  let q := (beta + 2) / beta
  let z := a * n * r * (beta * L) / m
  let w := mu0 * n * r * (beta * L) / m
  have hq : q <= 2 := by
    dsimp [q]
    apply (div_le_iff₀ hbeta0).mpr
    linarith
  have hz : 0 <= z := by dsimp [z]; positivity
  have hz1 : z <= 1 := by
    dsimp [z]
    exact (div_le_one hmpos).mpr hdensity
  have hzw : z <= w := by
    dsimp [z, w]
    apply div_le_div_of_nonneg_right _ hm
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha hn.le) hr)
      (mul_nonneg hbeta0.le hL)
  have hscale : (((beta + 2) * L) / (m / (n * s))) * (a * r / s) = q * z := by
    dsimp [q, z]
    field_simp
  have hroot : Real.sqrt (((beta + 2) * L) / (m / (n * s))) *
      Real.sqrt (a * r / s) = Real.sqrt (q * z) := by
    rw [← Real.sqrt_mul (by positivity : 0 <= ((beta + 2) * L) / (m / (n * s)))]
    rw [hscale]
  calc
    _ = C * E * ((Real.sqrt (((beta + 2) * L) / (m / (n * s))) *
        Real.sqrt (a * r / s)) * Bf +
      ((((beta + 2) * L) / (m / (n * s))) * (a * r / s)) * Be) := by ring
    _ = C * E * (Real.sqrt (q * z) * Bf + (q * z) * Be) := by rw [hroot, hscale]
    _ <= C * E * (2 * (Bf + Be) * Real.sqrt w) :=
      mul_le_mul_of_nonneg_left (scalar_absorption q z w Bf Be hq hz hz1 hzw hBf hBe)
        (mul_nonneg hC hE)
    _ = _ := by dsimp [w]; ring

end MatrixOffdiag

/- New exact probability conclusion: Conclusion.lean; SHA256 5a8269940ab603fc567f1c5aa4b733ef37cd15aa0d5510f14c3c008d1a0b2d51. -/
open MatrixCompletion
theorem solution :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max (Real.sqrt μ₀) μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              LinearNeumannOffDiagonalCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    Real.sqrt
                      ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                          (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Ce, hCe, hEntry⟩ := linear_neumann_off_diagonal_coefficient_base_entry_sup_norm_bound_min_dim
  obtain ⟨Cf, hCf, hFrob⟩ := linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min
  obtain ⟨Cp, cp, hCp, hcp, hPoint⟩ :=
    linear_neumann_off_diagonal_coefficient_pointwise_two_term_tail_from_min_dim_base_bounds Ce Cf hCe hCf
  obtain ⟨Ct, ct, hCt, hct, hUniform⟩ :=
    linear_neumann_off_diagonal_coefficient_uniform_two_term_bound_from_min_dim_shifted_pointwise_tails
      Cp cp Ce Cf hCp hcp
  refine ⟨2 * Ct * (Cf + Ce), ct, by positivity, hct, ?_⟩
  intro beta lam hbeta hlam n1 n2 r m M mu0 mu1 S hn1 hn2 hr hm hmu0 hmu1 hA0 hA1 hsample
  let a := min mu0 (mu1 ^ 2)
  obtain ⟨ha1, hAa⟩ := MatrixOffdiag.effective_coherence S mu0 mu1 hn1 hn2 hr hmu0 hmu1 hA0 hA1
  change 1 <= a at ha1
  change A0 S a at hAa
  have hRaw := hUniform 0 beta hbeta n1 n2 r m M a mu1 S hn1 hn2 hr hm ha1 hmu1 hAa hA1
    (by simp) (fun w => hPoint 0 beta hbeta n1 n2 r m M a mu1 S hn1 hn2 hr hm ha1 hmu1 hAa hA1
      (by simp) w
      (fun Omega2 => linear_neumann_off_diagonal_coefficient_entry_as_centered_scalar_fluctuation Omega2 S _ w)
      (hEntry n1 n2 r M a mu1 S hn1 hn2 hr ha1 hmu1 hAa hA1 w)
      (by simpa only [mul_div_assoc] using hFrob n1 n2 r M a mu1 S hn1 hn2 hr ha1 hmu1 hAa hA1 w))
  have hn : (0 : Real) < (max n1 n2 : Nat) := by
    exact_mod_cast lt_of_lt_of_le hn1 (le_max_left n1 n2)
  have hs : (0 : Real) < (min n1 n2 : Nat) := by exact_mod_cast lt_min hn1 hn2
  have hnOne : (1 : Real) <= (max n1 n2 : Nat) := by
    exact_mod_cast Nat.succ_le_of_lt (lt_of_lt_of_le hn1 (le_max_left n1 n2))
  have hlog : 0 <= Real.log (max n1 n2 : Nat) := Real.log_nonneg hnOne
  have hdim : ((max n1 n2 : Nat) : Real) * ((min n1 n2 : Nat) : Real) =
      (n1 : Real) * (n2 : Real) := by
    rcases le_total n1 n2 with h | h
    · rw [max_eq_right h, min_eq_left h]; ring
    · rw [max_eq_left h, min_eq_right h]
  have hdensity : a * (max n1 n2 : Nat) * (r : Real) *
      (beta * Real.log (max n1 n2 : Nat)) <= (m : Real) :=
    MatrixOffdiag.density_le_of_sample lam mu0 mu1 a _ _ _ _ hlam (by linarith)
      (min_le_right _ _) hn.le (by positivity) (mul_nonneg (by linarith) hlog) hsample
  have hBound := MatrixOffdiag.raw_threshold_le Cf Ce
    (mu1 * Real.sqrt ((r : Real) / ((n1 : Real) * (n2 : Real)))) Ct a mu0
    (max n1 n2 : Nat) (min n1 n2 : Nat) r m beta (Real.log (max n1 n2 : Nat))
    hCf.le hCe.le (by positivity) hCt.le (by linarith) (min_le_left _ _) hn hs
    (by positivity) (by positivity) hbeta hlog hdensity
  simp only [hdim, mul_assoc] at hBound
  rcases sample_ratio_between_zero_and_one n1 n2 m hn1 hn2 hm with ⟨hp0, hp1⟩
  apply le_trans hRaw
  refine bernoulli_event_probability_mono _ _ _ hp0 hp1 ?_
  intro Omega2 hOmega
  apply le_trans hOmega
  simpa only [mul_assoc] using hBound

