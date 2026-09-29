-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_centered_coefficient_entry_sup_event_tight_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T09:39:12.365749+00:00
-- url     : https://prove2.me/submissions/6f83ba49-363d-43d3-8569-6e94bd4118f3

import Theorems.Thm_scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales
import Theorems.Thm_quadratic_neumann_middle_index_distinct_centered_base_frobenius_norm_bound_min_dim
import Theorems.Thm_tangent_coordinate_kernel_bound_from_a0_min_dim
import Theorems.Thm_bernoulli_uniform_coordinate_bound_from_pointwise_tails_with_cardinality_factor
import Theorems.Thm_bernoulli_event_probability_mono
import Theorems.Thm_sample_ratio_between_zero_and_one
import Mathlib.Tactic

open MatrixCompletion

open scoped Classical BigOperators

/-!
# Tight `μ`-scale entrySup EVENT for the MIDDLE-index centered coefficient (min-dim)

Mirror of the first-index tight coefficient event, for the two-copy decoupled
centered `ω₁ = ω₃ ≠ ω₂` term (Lemma 6.7).  For each fixed output coordinate
`w = (i,j)`, the coefficient entry
`quadraticMiddleIndexDistinctCenteredCoefficientMatrix Ω2 S p i j` equals the
scalar centered sampling fluctuation over `Ω2` of the fixed **two-kernel** base

  `B^{(w)}_{ab} = if (a,b)=w then 0
                 else signMatrix S w.1 w.2 · K(w.1,w.2,a,b) · K(a,b,w.1,w.2)`,

whose entrySup (`signScale·kernelScale²`) and Frobenius (`signScale·kernelScale^{3/2}`)
scales are IDENTICAL to the first-index base.  The scalar-Bernstein keystone
converts these into a two-term tail; the `n₁n₂`-cardinality union (absorbed by
the `β → β+2` shift) yields the uniform entrySup event.

Source: Candès–Recht 2008, §6.3, PDF pp. 32--33, Lemma 6.7.
-/

namespace MatrixCompletion

/-- Per-entry representation: the `(i,j)` entry of the middle conditional
coefficient matrix is the scalar centered sampling fluctuation of the per-entry
two-kernel base. -/
private lemma coefficient_entry_as_matrixEntrySum
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega2 : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ)
    (i : Fin n₁) (j : Fin n₂) :
    quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S p i j =
      matrixEntrySum
        (centeredSamplingFluctuation Omega2 p
          (fun a b =>
            if (a, b) = (i, j) then 0
            else
              signMatrix S i j *
                tangentCoordinateKernel S i j a b *
                  tangentCoordinateKernel S a b i j)) := by
  classical
  by_cases hp : p = 0
  · unfold quadraticMiddleIndexDistinctCenteredCoefficientMatrix
      matrixEntrySum centeredSamplingFluctuation
    simp [hp]
  unfold quadraticMiddleIndexDistinctCenteredCoefficientMatrix
    matrixEntrySum centeredSamplingFluctuation samplingProjection
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w2 _
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  by_cases hw2 : w2 = (i, j)
  · simp [hw2]
  · have hne : (w2.1, w2.2) = (i, j) ↔ w2 = (i, j) := by
      constructor
      · intro h; exact Prod.ext (congrArg Prod.fst h) (congrArg Prod.snd h)
      · intro h; rw [h]
    by_cases hmem : w2 ∈ Omega2
    · simp only [hw2, if_false, hmem, if_true, centeredIndicator]
      field_simp [hp] <;> ring
    · simp only [hw2, if_false, hmem, if_false, centeredIndicator]
      field_simp [hp] <;> ring

/-- entrySup of the per-entry middle two-kernel base. -/
private lemma base_entry_sup_bound
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ μ₁ : ℝ) (Cker : ℝ)
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁)
    (hA0 : A0 S μ₀) (hA1 : A1 S μ₁) (hCker_pos : 0 < Cker)
    (hKernel : ∀ (i j a b : _),
      |tangentCoordinateKernel S i j a b| ≤ Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))))
    (i : Fin n₁) (j : Fin n₂) :
    entrySupNorm
        (fun a b =>
          if (a, b) = (i, j) then 0
          else
            signMatrix S i j *
              tangentCoordinateKernel S i j a b *
                tangentCoordinateKernel S a b i j) ≤
      (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) *
          (Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  set signScale : ℝ := μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
    with hsignScale
  set kernelScale : ℝ := Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) with hkernelScale
  have hsignScale_nonneg : 0 ≤ signScale := by rw [hsignScale]; positivity
  have hkernelScale_nonneg : 0 ≤ kernelScale := by
    rw [hkernelScale]
    have hμ₀nn : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
    positivity
  unfold entrySupNorm
  apply ciSup_le
  intro a
  apply ciSup_le
  intro b
  simp only
  by_cases hab : (a, b) = (i, j)
  · rw [if_pos hab, abs_zero]
    positivity
  · rw [if_neg hab]
    -- |sign · K(ij,ab) · K(ab,ij)| ≤ signScale · kernelScale · kernelScale
    have hSign : |signMatrix S i j| ≤ signScale := by
      rw [hsignScale]; exact hA1 i j
    have hK1 : |tangentCoordinateKernel S i j a b| ≤ kernelScale := by
      rw [hkernelScale]; exact hKernel i j a b
    have hK2 : |tangentCoordinateKernel S a b i j| ≤ kernelScale := by
      rw [hkernelScale]; exact hKernel a b i j
    calc
      |signMatrix S i j * tangentCoordinateKernel S i j a b *
          tangentCoordinateKernel S a b i j|
          = |signMatrix S i j| * |tangentCoordinateKernel S i j a b| *
              |tangentCoordinateKernel S a b i j| := by
            rw [abs_mul, abs_mul]
      _ ≤ signScale * kernelScale * kernelScale := by
            apply mul_le_mul _ hK2 (abs_nonneg _) (by positivity)
            exact mul_le_mul hSign hK1 (abs_nonneg _) hsignScale_nonneg

end MatrixCompletion

/-- Tight `μ`-scale entrySup event for the MIDDLE-index centered coefficient
matrix. -/
theorem solution :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega2 =>
              QuadraticMiddleIndexDistinctCenteredCoefficientBound Omega2 S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (Ccoef *
                  (Real.sqrt
                      (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                          (μ₀ * (r : ℝ) / (↑(min n₁ n₂)))) +
                    (((β + 2) * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                      (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                        (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
                          (μ₀ * (r : ℝ) / (↑(min n₁ n₂))))))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales with
    ⟨Cbern, cbern, hCbern, hcbern, hBernstein⟩
  rcases (quadratic_neumann_middle_index_distinct_centered_base_frobenius_norm_bound_min_dim :
      ∃ Cfro : ℝ, 0 < Cfro ∧ _) with ⟨Cfro, hCfro, hFrobBase⟩
  rcases tangent_coordinate_kernel_bound_from_a0_min_dim with ⟨Cker, hCker, hKernel⟩
  refine ⟨Cbern * max Cfro (Cker ^ 2), cbern, by positivity, hcbern, ?_⟩
  intro β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hm hμ₀ hμ₁ hA0 hA1
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  rcases sample_ratio_between_zero_and_one n₁ n₂ m hn₁ hn₂ hm with
    ⟨hp_nonneg, hp_le_one⟩
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set N : ℝ := (↑(max n₁ n₂) : ℝ) with hN
  set Cmax : ℝ := max Cfro (Cker ^ 2) with hCmax
  have hCmax_pos : 0 < Cmax := lt_max_of_lt_left hCfro
  have hKer' : ∀ (i j a b : _),
      |tangentCoordinateKernel S i j a b| ≤ Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
    intro i j a b
    exact hKernel n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j a b
  have hβ2 : 2 < β + 2 := by linarith
  set frobScaleTight : ℝ :=
    μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
      Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
        (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) with hfrobScaleTight
  set entryScaleTight : ℝ :=
    μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
      (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
        (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) with hentryScaleTight
  set entryScaleRaw : ℝ :=
    (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
      (Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) *
        (Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) with hentryScaleRaw
  set frobScaleRaw : ℝ :=
    Cfro * μ₁ *
      Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
        Real.sqrt (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
          (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) with hfrobScaleRaw
  set rawTwoTerm : ℝ :=
    Real.sqrt (((β + 2) * Real.log N) / p) * frobScaleRaw +
      (((β + 2) * Real.log N) / p) * entryScaleRaw with hrawTwoTerm
  set targetTwoTerm : ℝ :=
    Real.sqrt (((β + 2) * Real.log N) / p) * frobScaleTight +
      (((β + 2) * Real.log N) / p) * entryScaleTight with htargetTwoTerm
  have hμ₀nn : 0 ≤ μ₀ := le_trans zero_le_one hμ₀
  have hμ₁nn : 0 ≤ μ₁ := le_trans zero_le_one hμ₁
  have hfrobScaleTight_nonneg : 0 ≤ frobScaleTight := by rw [hfrobScaleTight]; positivity
  have hentryScaleTight_nonneg : 0 ≤ entryScaleTight := by rw [hentryScaleTight]; positivity
  have hPoint : ∀ w : Fin n₁ × Fin n₂,
      bernoulliEventProb p
          (fun Omega2 =>
            |quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S p w.1 w.2| ≤
              Cbern * rawTwoTerm) ≥
        1 - cbern * Real.rpow N (-(β + 2)) := by
    intro w
    have hRep :
        ∀ Omega : Finset (Fin n₁ × Fin n₂),
          (fun Omega =>
            quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega S p w.1 w.2)
              Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega p
                (fun a b =>
                  if (a, b) = (w.1, w.2) then 0
                  else
                    signMatrix S w.1 w.2 *
                      tangentCoordinateKernel S w.1 w.2 a b *
                        tangentCoordinateKernel S a b w.1 w.2)) := by
      intro Omega
      exact coefficient_entry_as_matrixEntrySum Omega S p w.1 w.2
    have hEntry :
        entrySupNorm
            (fun a b =>
              if (a, b) = (w.1, w.2) then 0
              else
                signMatrix S w.1 w.2 *
                  tangentCoordinateKernel S w.1 w.2 a b *
                    tangentCoordinateKernel S a b w.1 w.2) ≤ entryScaleRaw := by
      rw [hentryScaleRaw]
      exact base_entry_sup_bound S μ₀ μ₁ Cker hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 hCker hKer' w.1 w.2
    have hFrob :
        frobeniusNorm
            (fun a b =>
              if (a, b) = (w.1, w.2) then 0
              else
                signMatrix S w.1 w.2 *
                  tangentCoordinateKernel S w.1 w.2 a b *
                    tangentCoordinateKernel S a b w.1 w.2) ≤ frobScaleRaw := by
      rw [hfrobScaleRaw]
      exact hFrobBase n₁ n₂ r M μ₀ μ₁ S hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 w
    have hRaw :=
      hBernstein (β + 2) hβ2 n₁ n₂ m hn₁ hn₂ hm
        (fun Omega =>
          quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega S p w.1 w.2)
        (fun a b =>
          if (a, b) = (w.1, w.2) then 0
          else
            signMatrix S w.1 w.2 *
              tangentCoordinateKernel S w.1 w.2 a b *
                tangentCoordinateKernel S a b w.1 w.2)
        entryScaleRaw frobScaleRaw hRep hEntry hFrob
    simpa [hp, hN, hrawTwoTerm, mul_assoc] using hRaw
  have hUnion :=
    bernoulli_uniform_coordinate_bound_from_pointwise_tails_with_cardinality_factor
      Cbern cbern hCbern hcbern p rawTwoTerm (Real.rpow N (-(β + 2)))
      hp_nonneg hp_le_one n₁ n₂
      (fun w Omega =>
        quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega S p w.1 w.2)
      hPoint
  have hCardFail :
      ((Fintype.card (Fin n₁ × Fin n₂) : ℝ) * cbern) * Real.rpow N (-(β + 2)) ≤
        cbern * Real.rpow N (-β) := by
    have hN_pos_nat : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
    have hN_pos : 0 < N := by rw [hN]; exact_mod_cast hN_pos_nat
    have hN_ge_one : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hN_pos_nat
    have hcard_eq :
        (Fintype.card (Fin n₁ × Fin n₂) : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
      simp [Fintype.card_prod, Fintype.card_fin]
    have hprod_le_N2 : (n₁ : ℝ) * (n₂ : ℝ) ≤ N ^ 2 := by
      have h1 : (n₁ : ℝ) ≤ N := by rw [hN]; exact_mod_cast Nat.le_max_left n₁ n₂
      have h2 : (n₂ : ℝ) ≤ N := by rw [hN]; exact_mod_cast Nat.le_max_right n₁ n₂
      nlinarith [Nat.cast_nonneg (α := ℝ) n₁, Nat.cast_nonneg (α := ℝ) n₂,
        le_trans zero_le_one hN_ge_one]
    have hcard_le_N2 :
        (Fintype.card (Fin n₁ × Fin n₂) : ℝ) ≤ N ^ 2 := by
      rw [hcard_eq]; exact hprod_le_N2
    have hN2_rpow : N ^ 2 = Real.rpow N 2 := by
      have := Real.rpow_natCast N 2; simpa using this.symm
    have hrpow_combine :
        Real.rpow N 2 * Real.rpow N (-(β + 2)) = Real.rpow N (-β) := by
      rw [show Real.rpow N 2 = N ^ (2 : ℝ) from rfl,
        show Real.rpow N (-(β + 2)) = N ^ (-(β + 2) : ℝ) from rfl,
        show Real.rpow N (-β) = N ^ (-β : ℝ) from rfl, ← Real.rpow_add hN_pos]
      congr 1; ring
    have hrpow_pos : 0 < Real.rpow N (-(β + 2)) := Real.rpow_pos_of_pos hN_pos _
    have hcbern_nonneg : 0 ≤ cbern := le_of_lt hcbern
    calc ((Fintype.card (Fin n₁ × Fin n₂) : ℝ) * cbern) * Real.rpow N (-(β + 2))
        ≤ (N ^ 2 * cbern) * Real.rpow N (-(β + 2)) := by
          apply mul_le_mul_of_nonneg_right _ (le_of_lt hrpow_pos)
          exact mul_le_mul_of_nonneg_right hcard_le_N2 hcbern_nonneg
      _ = cbern * (Real.rpow N 2 * Real.rpow N (-(β + 2))) := by rw [hN2_rpow]; ring
      _ = cbern * Real.rpow N (-β) := by rw [hrpow_combine]
  have hUnion' :
      bernoulliEventProb p
          (fun Omega2 =>
            ∀ w : Fin n₁ × Fin n₂,
              |quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S p w.1 w.2| ≤
                Cbern * rawTwoTerm) ≥
        1 - cbern * Real.rpow N (-β) := by
    have hge :
        (1 : ℝ) - cbern * Real.rpow N (-β) ≤
          1 - ((Fintype.card (Fin n₁ × Fin n₂) : ℝ) * cbern) * Real.rpow N (-(β + 2)) := by
      linarith [hCardFail]
    exact le_trans hge hUnion
  have hRawTwoTerm_le : Cbern * rawTwoTerm ≤ Cbern * (Cmax * targetTwoTerm) := by
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hCbern)
    have hlogfactor_nonneg : 0 ≤ Real.sqrt (((β + 2) * Real.log N) / p) := Real.sqrt_nonneg _
    have hlogdiv_nonneg : 0 ≤ ((β + 2) * Real.log N) / p := by
      have hlogN : 0 ≤ Real.log N := by
        apply Real.log_nonneg
        rw [hN]
        have : 1 ≤ max n₁ n₂ := le_trans hn₁ (Nat.le_max_left _ _)
        exact_mod_cast this
      positivity
    have hfrobRaw_eq : frobScaleRaw = Cfro * frobScaleTight := by
      rw [hfrobScaleRaw, hfrobScaleTight]; ring
    have hentryRaw_eq : entryScaleRaw = Cker ^ 2 * entryScaleTight := by
      rw [hentryScaleRaw, hentryScaleTight]; ring
    have hfro_le : Cfro ≤ Cmax := le_max_left _ _
    have hcker2_le : Cker ^ 2 ≤ Cmax := le_max_right _ _
    have hfrob_le : frobScaleRaw ≤ Cmax * frobScaleTight := by
      rw [hfrobRaw_eq]
      exact mul_le_mul_of_nonneg_right hfro_le hfrobScaleTight_nonneg
    have hentry_le : entryScaleRaw ≤ Cmax * entryScaleTight := by
      rw [hentryRaw_eq]
      exact mul_le_mul_of_nonneg_right hcker2_le hentryScaleTight_nonneg
    calc rawTwoTerm
        = Real.sqrt (((β + 2) * Real.log N) / p) * frobScaleRaw +
            (((β + 2) * Real.log N) / p) * entryScaleRaw := hrawTwoTerm
      _ ≤ Real.sqrt (((β + 2) * Real.log N) / p) * (Cmax * frobScaleTight) +
            (((β + 2) * Real.log N) / p) * (Cmax * entryScaleTight) := by
            apply add_le_add
            · exact mul_le_mul_of_nonneg_left hfrob_le hlogfactor_nonneg
            · exact mul_le_mul_of_nonneg_left hentry_le hlogdiv_nonneg
      _ = Cmax * (Real.sqrt (((β + 2) * Real.log N) / p) * frobScaleTight +
            (((β + 2) * Real.log N) / p) * entryScaleTight) := by ring
      _ = Cmax * targetTwoTerm := by rw [htargetTwoTerm]
  have hFinalMono :
      bernoulliEventProb p
          (fun Omega2 =>
            ∀ w : Fin n₁ × Fin n₂,
              |quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S p w.1 w.2| ≤
                Cbern * rawTwoTerm) ≤
        bernoulliEventProb p
          (fun Omega2 =>
            QuadraticMiddleIndexDistinctCenteredCoefficientBound Omega2 S p
              (Cbern * max Cfro (Cker ^ 2) * targetTwoTerm)) := by
    refine bernoulli_event_probability_mono p _ _ hp_nonneg hp_le_one ?_
    intro Omega2 hAll
    unfold QuadraticMiddleIndexDistinctCenteredCoefficientBound entrySupNorm
    apply ciSup_le; intro i; apply ciSup_le; intro j
    have hbnd := hAll (i, j)
    calc |quadraticMiddleIndexDistinctCenteredCoefficientMatrix Omega2 S p i j|
        ≤ Cbern * rawTwoTerm := hbnd
      _ ≤ Cbern * (Cmax * targetTwoTerm) := hRawTwoTerm_le
      _ = Cbern * max Cfro (Cker ^ 2) * targetTwoTerm := by rw [hCmax]; ring
  have hcombined := le_trans hUnion' hFinalMono
  rw [hp, hN] at hcombined ⊢
  simpa [htargetTwoTerm, hfrobScaleTight, hentryScaleTight, mul_assoc] using hcombined
