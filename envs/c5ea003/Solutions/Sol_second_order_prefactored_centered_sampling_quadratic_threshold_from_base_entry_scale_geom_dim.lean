-- Prove2me | solution 1 for second_order_prefactored_centered_sampling_quadratic_threshold_from_base_entry_scale_geom_dim
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-07-04T12:39:17.86398+00:00
-- url     : https://prove2.me/submissions/6fcce985-d0d7-4bc5-81e9-08a42e72b160

import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.Complex.ExponentialBounds

open MatrixCompletion

/-- G3: geometric-scale second-order prefactored threshold. -/
theorem solution
    (Cfixed Cbase : ℝ) :
    0 < Cfixed → 0 < Cbase →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ (Omega : Finset (Fin n₁ × Fin n₂))
          (B Y : Matrix (Fin n₁) (Fin n₂) ℝ),
        Y =
          ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) ^ 2 *
              (1 - 3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                3 * ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ^ 2)) •
            centeredSamplingFluctuation Omega
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B →
        entrySupNorm B ≤
          Cbase * μ₀ ^ 3 * (r : ℝ) ^ 3 /
            ((↑(min n₁ n₂)) ^ 2 * Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) →
        CenteredSamplingSpectralBound Omega
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B
            (Cfixed * Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              entrySupNorm B) →
        spectralNorm Y ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hCf hCb
  -- small-context scalar helpers
  have one_le_mul' : ∀ {a b : ℝ}, 1 ≤ a → 1 ≤ b → 1 ≤ a * b := by
    intro a b ha hb
    calc (1 : ℝ) = 1 * 1 := (one_mul 1).symm
      _ ≤ a * b := mul_le_mul ha hb zero_le_one (le_trans zero_le_one ha)
  have quad_pos' : ∀ q : ℝ, (0 : ℝ) < 1 - 3 * q + 3 * q ^ 2 := by
    intro q
    have h : 1 - 3 * q + 3 * q ^ 2 = 3 * (q - 1 / 2) ^ 2 + 1 / 4 := by ring
    rw [h]; positivity
  have quad_le_one' : ∀ q : ℝ, 0 ≤ q → q ≤ 1 → 1 - 3 * q + 3 * q ^ 2 ≤ 1 := by
    intro q hq0 hq1
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hq1)]
  have rpow43_cube : ∀ x : ℝ, 0 < x → 1 ≤ x →
      x ^ 3 ≤ (Real.rpow x ((4 : ℝ) / 3)) ^ 2 *
        Real.sqrt (Real.rpow x ((4 : ℝ) / 3)) := by
    intro x hx0 hx1
    have hnot : Real.rpow x ((4 : ℝ) / 3) = x ^ ((4 : ℝ) / 3) := rfl
    rw [hnot]
    have h2 : (x ^ ((4 : ℝ) / 3)) ^ (2 : ℕ) = x ^ ((8 : ℝ) / 3) := by
      rw [← Real.rpow_natCast (x ^ ((4 : ℝ) / 3)) 2,
        ← Real.rpow_mul (le_of_lt hx0)]
      norm_num
    have hs : Real.sqrt (x ^ ((4 : ℝ) / 3)) = x ^ ((2 : ℝ) / 3) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hx0)]
      norm_num
    have hc : x ^ (3 : ℕ) = x ^ ((3 : ℝ)) := by
      rw [← Real.rpow_natCast x 3]; norm_num
    rw [h2, hs, hc, ← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    norm_num
  refine ⟨Cfixed * Cbase, by positivity, ?_⟩
  intro β lam hβ hlam n₁ n₂ r m μ₀ hn₁ hn₂ hr hm hμ₀ hsample Omega B Y hY hB hcsf
  have hlam0 : (0 : ℝ) < lam := lt_of_lt_of_le one_pos hlam
  have hrpowlam : (0 : ℝ) < Real.rpow lam (-((3 : ℝ) / 2)) :=
    Real.rpow_pos_of_pos hlam0 _
  have hn₁R : (0 : ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn₂R : (0 : ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hμ₀0 : (0 : ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hrR1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrR0 : (0 : ℝ) < (r : ℝ) := lt_of_lt_of_le one_pos hrR1
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp_def
  -- spectral norm of a scalar multiple
  have hsmul : ∀ (c : ℝ) (X : Matrix (Fin n₁) (Fin n₂) ℝ),
      spectralNorm (c • X) = |c| * spectralNorm X := by
    intro c X
    unfold spectralNorm
    rw [map_smul, map_smul, norm_smul, Real.norm_eq_abs]
  have hcsf_nonneg : 0 ≤ spectralNorm (centeredSamplingFluctuation Omega p B) := by
    unfold spectralNorm; exact norm_nonneg _
  have hYnorm : spectralNorm Y =
      |(p⁻¹) ^ 2 * (1 - 3 * p + 3 * p ^ 2)| *
        spectralNorm (centeredSamplingFluctuation Omega p B) := by
    rw [hY, hsmul]
  -- unfold the centered sampling hypothesis
  unfold CenteredSamplingSpectralBound at hcsf
  by_cases hmax1 : max n₁ n₂ = 1
  · -- degenerate case: n₁ = n₂ = 1, log term vanishes
    have hlog0 : Real.log (↑(max n₁ n₂) : ℝ) = 0 := by
      rw [hmax1]; simp
    have hbound0 : Cfixed * Real.sqrt
        ((β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂))) / p) *
        entrySupNorm B = 0 := by
      rw [hlog0]
      simp
    have hzero : spectralNorm (centeredSamplingFluctuation Omega p B) = 0 := by
      rw [hbound0] at hcsf
      exact le_antisymm hcsf hcsf_nonneg
    rw [hYnorm, hzero, mul_zero]
    positivity
  · -- main case: max n₁ n₂ ≥ 2
    have hmax_ge1 : 1 ≤ max n₁ n₂ := le_max_of_le_left hn₁
    have hmax2 : 2 ≤ max n₁ n₂ := by omega
    have hnR2 : (2 : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by exact_mod_cast hmax2
    have hmn_pos : 0 < min n₁ n₂ := lt_min hn₁ hn₂
    have hmnR0' : (0 : ℝ) < (↑(min n₁ n₂) : ℝ) := by exact_mod_cast hmn_pos
    set nR : ℝ := (↑(max n₁ n₂) : ℝ) with hnR_def
    set mnR : ℝ := (↑(min n₁ n₂) : ℝ) with hmnR_def
    have hnR0 : (0 : ℝ) < nR := lt_of_lt_of_le two_pos hnR2
    have hmnR0 : (0 : ℝ) < mnR := hmnR0'
    -- log 2 > 1/2 via exp(1/2) < 2
    have hexp_half : Real.exp ((1 : ℝ) / 2) < 2 := by
      have hsq : Real.exp ((1 : ℝ) / 2) * Real.exp ((1 : ℝ) / 2) = Real.exp 1 := by
        rw [← Real.exp_add]; norm_num
      nlinarith [Real.exp_one_lt_d9, Real.exp_pos ((1 : ℝ) / 2)]
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 :=
      (Real.lt_log_iff_exp_lt two_pos).mpr hexp_half
    have hloglog : Real.log 2 ≤ Real.log nR := Real.log_le_log two_pos hnR2
    have hlognR : (1 : ℝ) / 2 < Real.log nR := lt_of_lt_of_le hlog2 hloglog
    have hlognR0 : (0 : ℝ) < Real.log nR := by linarith
    -- opaque abbreviations (no defeq value, only defining equations)
    obtain ⟨L, hL_def⟩ : ∃ x : ℝ, x = β * Real.log nR := ⟨_, rfl⟩
    obtain ⟨U, hU_def⟩ : ∃ x : ℝ, x = Real.rpow μ₀ ((4 : ℝ) / 3) := ⟨_, rfl⟩
    obtain ⟨V, hV_def⟩ : ∃ x : ℝ, x = Real.rpow (r : ℝ) ((4 : ℝ) / 3) := ⟨_, rfl⟩
    rw [← hU_def, ← hV_def, ← hL_def] at hsample
    have hL1 : (1 : ℝ) ≤ L := by
      rw [hL_def]
      calc (1 : ℝ) = 2 * (1 / 2) := by norm_num
        _ ≤ β * Real.log nR :=
            mul_le_mul (le_of_lt hβ) (le_of_lt hlognR) (by norm_num)
              (le_trans (by norm_num) (le_of_lt hβ))
    have hL0 : (0 : ℝ) < L := lt_of_lt_of_le one_pos hL1
    have hU1 : (1 : ℝ) ≤ U := by
      rw [hU_def]
      calc (1 : ℝ) = Real.rpow μ₀ 0 := (Real.rpow_zero μ₀).symm
        _ ≤ Real.rpow μ₀ ((4 : ℝ) / 3) :=
            Real.rpow_le_rpow_of_exponent_le hμ₀ (by norm_num)
    have hV1 : (1 : ℝ) ≤ V := by
      rw [hV_def]
      calc (1 : ℝ) = Real.rpow (r : ℝ) 0 := (Real.rpow_zero _).symm
        _ ≤ Real.rpow (r : ℝ) ((4 : ℝ) / 3) :=
            Real.rpow_le_rpow_of_exponent_le hrR1 (by norm_num)
    have hU0 : (0 : ℝ) < U := lt_of_lt_of_le one_pos hU1
    have hV0 : (0 : ℝ) < V := lt_of_lt_of_le one_pos hV1
    -- the rpow cube comparisons, proved on raw rpow form and transported
    have hUcube : μ₀ ^ 3 ≤ U ^ 2 * Real.sqrt U := by
      rw [hU_def]; exact rpow43_cube μ₀ hμ₀0 hμ₀
    have hVcube : (r : ℝ) ^ 3 ≤ V ^ 2 * Real.sqrt V := by
      rw [hV_def]; exact rpow43_cube (r : ℝ) hrR0 hrR1
    obtain ⟨K, hK_def⟩ : ∃ x : ℝ, x = lam * U * V * L := ⟨_, rfl⟩
    have hK1 : (1 : ℝ) ≤ K := by
      rw [hK_def]
      exact one_le_mul' (one_le_mul' (one_le_mul' hlam hU1) hV1) hL1
    have hK0 : (0 : ℝ) < K := lt_of_lt_of_le one_pos hK1
    -- m > 0, p ∈ (0, 1]
    have hm_pos : (0 : ℝ) < (m : ℝ) := by
      refine lt_of_lt_of_le ?_ hsample
      exact mul_pos (mul_pos (mul_pos (mul_pos hlam0 hU0) hnR0) hV0) hL0
    have hp_pos : 0 < p := div_pos hm_pos (mul_pos hn₁R hn₂R)
    have hp_le1 : p ≤ 1 := by
      rw [hp_def, div_le_one (mul_pos hn₁R hn₂R)]
      calc (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hm
        _ = (n₁ : ℝ) * (n₂ : ℝ) := by push_cast; ring
    -- product of max and min casts
    have hmaxmin : nR * mnR = (n₁ : ℝ) * (n₂ : ℝ) := by
      rw [hnR_def, hmnR_def]
      rcases le_total n₁ n₂ with h | h
      · rw [max_eq_right h, min_eq_left h]; try ring
      · rw [max_eq_left h, min_eq_right h]; try ring
    -- lower bound on p
    have hp_low : K / mnR ≤ p := by
      rw [div_le_iff₀ hmnR0, hp_def, div_mul_eq_mul_div,
        le_div_iff₀ (mul_pos hn₁R hn₂R)]
      calc K * ((n₁ : ℝ) * (n₂ : ℝ)) = K * (nR * mnR) := by rw [hmaxmin]
        _ = (lam * U * nR * V * L) * mnR := by rw [hK_def]; ring
        _ ≤ (m : ℝ) * mnR := mul_le_mul_of_nonneg_right hsample (le_of_lt hmnR0)
    obtain ⟨A, hA_def⟩ : ∃ x : ℝ, x = p⁻¹ := ⟨_, rfl⟩
    obtain ⟨D, hD_def⟩ : ∃ x : ℝ, x = mnR / K := ⟨_, rfl⟩
    have hA0 : (0 : ℝ) < A := by rw [hA_def]; exact inv_pos.mpr hp_pos
    have hD0 : (0 : ℝ) < D := by rw [hD_def]; exact div_pos hmnR0 hK0
    have hA_le_D : A ≤ D := by
      have hKm : (0 : ℝ) < K / mnR := div_pos hK0 hmnR0
      have h1d := one_div_le_one_div_of_le hKm hp_low
      rw [hA_def, hD_def]
      calc p⁻¹ = 1 / p := (one_div p).symm
        _ ≤ 1 / (K / mnR) := h1d
        _ = mnR / K := by rw [one_div_div]
    -- quadratic prefactor is at most A²
    have hquad_pos : (0 : ℝ) < 1 - 3 * p + 3 * p ^ 2 := quad_pos' p
    have hquad_le1 : 1 - 3 * p + 3 * p ^ 2 ≤ 1 :=
      quad_le_one' p (le_of_lt hp_pos) hp_le1
    have hpinv2 : (0 : ℝ) < (p⁻¹) ^ 2 := pow_pos (inv_pos.mpr hp_pos) 2
    have hpref : |(p⁻¹) ^ 2 * (1 - 3 * p + 3 * p ^ 2)| ≤ A ^ 2 := by
      rw [abs_of_pos (mul_pos hpinv2 hquad_pos)]
      calc (p⁻¹) ^ 2 * (1 - 3 * p + 3 * p ^ 2) ≤ (p⁻¹) ^ 2 * 1 :=
            mul_le_mul_of_nonneg_left hquad_le1 (le_of_lt hpinv2)
        _ = A ^ 2 := by rw [hA_def]; ring
    -- rewrite the sqrt argument
    have hsqrt_arg : (β * nR * Real.log nR) / p = L * nR * A := by
      rw [hL_def, hA_def, div_eq_mul_inv]; ring
    -- nonnegativity helpers
    have hsA : (0 : ℝ) ≤ Real.sqrt A := Real.sqrt_nonneg _
    have hsD : (0 : ℝ) ≤ Real.sqrt D := Real.sqrt_nonneg _
    have hsL : (0 : ℝ) ≤ Real.sqrt L := Real.sqrt_nonneg _
    have hsK : (0 : ℝ) < Real.sqrt K := Real.sqrt_pos.mpr hK0
    have hsmn : (0 : ℝ) < Real.sqrt mnR := Real.sqrt_pos.mpr hmnR0
    have hsnR : (0 : ℝ) < Real.sqrt nR := Real.sqrt_pos.mpr hnR0
    have hslam : (0 : ℝ) < Real.sqrt lam := Real.sqrt_pos.mpr hlam0
    have hsU : (0 : ℝ) < Real.sqrt U := Real.sqrt_pos.mpr hU0
    have hsV : (0 : ℝ) < Real.sqrt V := Real.sqrt_pos.mpr hV0
    have hscale_nonneg : (0 : ℝ) ≤ Cbase * μ₀ ^ 3 * (r : ℝ) ^ 3 /
        (mnR ^ 2 * Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))) := by
      apply div_nonneg
      · positivity
      · exact mul_nonneg (pow_nonneg (le_of_lt hmnR0) 2) (Real.sqrt_nonneg _)
    have hsLnRA : (0 : ℝ) ≤ Real.sqrt (L * nR * A) := Real.sqrt_nonneg _
    -- assemble the norm chain
    have hchain : spectralNorm Y ≤
        A ^ 2 * (Cfixed * Real.sqrt (L * nR * A) *
          (Cbase * μ₀ ^ 3 * (r : ℝ) ^ 3 /
            (mnR ^ 2 * Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))))) := by
      rw [hYnorm]
      have h1 : spectralNorm (centeredSamplingFluctuation Omega p B) ≤
          Cfixed * Real.sqrt (L * nR * A) *
            (Cbase * μ₀ ^ 3 * (r : ℝ) ^ 3 /
              (mnR ^ 2 * Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)))) := by
        calc spectralNorm (centeredSamplingFluctuation Omega p B)
            ≤ Cfixed * Real.sqrt ((β * nR * Real.log nR) / p) * entrySupNorm B :=
              hcsf
          _ = Cfixed * Real.sqrt (L * nR * A) * entrySupNorm B := by
              rw [hsqrt_arg]
          _ ≤ Cfixed * Real.sqrt (L * nR * A) *
              (Cbase * μ₀ ^ 3 * (r : ℝ) ^ 3 /
                (mnR ^ 2 * Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)))) := by
              apply mul_le_mul_of_nonneg_left hB
              exact mul_nonneg (le_of_lt hCf) hsLnRA
      exact mul_le_mul hpref h1 hcsf_nonneg (pow_nonneg (le_of_lt hA0) 2)
    -- scalar absorption: A²·√(L·nR·A)·μ₀³r³/(mn²·√(n₁n₂)) ≤ lam^{-3/2}
    have hscalar : A ^ 2 * Real.sqrt (L * nR * A) * (μ₀ ^ 3 * (r : ℝ) ^ 3 /
        (mnR ^ 2 * Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
        Real.rpow lam (-((3 : ℝ) / 2)) := by
      have hsqrtA : Real.sqrt (L * nR * A) = Real.sqrt (L * nR) * Real.sqrt A := by
        rw [Real.sqrt_mul (mul_nonneg (le_of_lt hL0) (le_of_lt hnR0))]
      have hmono : A ^ 2 * Real.sqrt A ≤ D ^ 2 * Real.sqrt D :=
        mul_le_mul (pow_le_pow_left₀ (le_of_lt hA0) hA_le_D 2)
          (Real.sqrt_le_sqrt hA_le_D) hsA (pow_nonneg (le_of_lt hD0) 2)
      have hsqrt_nn : Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)) =
          Real.sqrt nR * Real.sqrt mnR := by
        rw [← hmaxmin, Real.sqrt_mul (le_of_lt hnR0)]
      have hfactor : (0 : ℝ) ≤ Real.sqrt (L * nR) * (μ₀ ^ 3 * (r : ℝ) ^ 3 /
          (mnR ^ 2 * (Real.sqrt nR * Real.sqrt mnR))) := by
        apply mul_nonneg (Real.sqrt_nonneg _)
        apply div_nonneg
        · positivity
        · exact mul_nonneg (pow_nonneg (le_of_lt hmnR0) 2)
            (mul_nonneg (le_of_lt hsnR) (le_of_lt hsmn))
      have hLHS_le : A ^ 2 * Real.sqrt (L * nR * A) * (μ₀ ^ 3 * (r : ℝ) ^ 3 /
          (mnR ^ 2 * Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ)))) ≤
          D ^ 2 * Real.sqrt D * (Real.sqrt (L * nR) * (μ₀ ^ 3 * (r : ℝ) ^ 3 /
            (mnR ^ 2 * (Real.sqrt nR * Real.sqrt mnR)))) := by
        rw [hsqrtA, hsqrt_nn]
        calc A ^ 2 * (Real.sqrt (L * nR) * Real.sqrt A) *
            (μ₀ ^ 3 * (r : ℝ) ^ 3 / (mnR ^ 2 * (Real.sqrt nR * Real.sqrt mnR)))
            = (A ^ 2 * Real.sqrt A) * (Real.sqrt (L * nR) *
              (μ₀ ^ 3 * (r : ℝ) ^ 3 /
                (mnR ^ 2 * (Real.sqrt nR * Real.sqrt mnR)))) := by ring
          _ ≤ (D ^ 2 * Real.sqrt D) * (Real.sqrt (L * nR) *
              (μ₀ ^ 3 * (r : ℝ) ^ 3 /
                (mnR ^ 2 * (Real.sqrt nR * Real.sqrt mnR)))) :=
              mul_le_mul_of_nonneg_right hmono hfactor
          _ = D ^ 2 * Real.sqrt D * (Real.sqrt (L * nR) * (μ₀ ^ 3 * (r : ℝ) ^ 3 /
              (mnR ^ 2 * (Real.sqrt nR * Real.sqrt mnR)))) := by ring
      refine hLHS_le.trans ?_
      -- substitute D = mnR / K and simplify to √L·μ₀³·r³/(K²·√K)
      have hsimp : D ^ 2 * Real.sqrt D * (Real.sqrt (L * nR) * (μ₀ ^ 3 * (r : ℝ) ^ 3 /
          (mnR ^ 2 * (Real.sqrt nR * Real.sqrt mnR)))) =
          Real.sqrt L * μ₀ ^ 3 * (r : ℝ) ^ 3 / (K ^ 2 * Real.sqrt K) := by
        rw [hD_def, div_pow, Real.sqrt_div' mnR (le_of_lt hK0),
          Real.sqrt_mul (le_of_lt hL0)]
        field_simp [ne_of_gt hK0, ne_of_gt hsK, ne_of_gt hsmn, ne_of_gt hsnR,
          ne_of_gt hmnR0]
        try ring
      rw [hsimp]
      -- final comparison: √L·μ₀³·r³/(K²·√K) ≤ lam^{-3/2}
      have hrpow_expand : Real.rpow lam (-((3 : ℝ) / 2)) =
          1 / (lam * Real.sqrt lam) := by
        rw [show Real.rpow lam (-((3 : ℝ) / 2)) = lam ^ (-((3 : ℝ) / 2)) from rfl,
          Real.rpow_neg (le_of_lt hlam0), one_div]
        congr 1
        have h32 : ((3 : ℝ) / 2) = 1 + 1 / 2 := by norm_num
        rw [h32, Real.rpow_add hlam0, Real.rpow_one, ← Real.sqrt_eq_rpow]
      rw [hrpow_expand,
        div_le_div_iff₀ (mul_pos (pow_pos hK0 2) hsK) (mul_pos hlam0 hslam),
        one_mul]
      -- goal: √L·μ₀³·r³·(lam·√lam) ≤ K²·√K
      have hsqrtK : Real.sqrt K = Real.sqrt lam * Real.sqrt U * Real.sqrt V *
          Real.sqrt L := by
        rw [hK_def,
          Real.sqrt_mul (mul_nonneg (mul_nonneg (le_of_lt hlam0) (le_of_lt hU0))
            (le_of_lt hV0)),
          Real.sqrt_mul (mul_nonneg (le_of_lt hlam0) (le_of_lt hU0)),
          Real.sqrt_mul (le_of_lt hlam0)]
      have hK2 : K ^ 2 = lam ^ 2 * U ^ 2 * V ^ 2 * L ^ 2 := by
        rw [hK_def]; ring
      have hlam_sq : lam ≤ lam ^ 2 := by
        calc lam = lam * 1 := (mul_one lam).symm
          _ ≤ lam * lam := mul_le_mul_of_nonneg_left hlam (le_of_lt hlam0)
          _ = lam ^ 2 := (pow_two lam).symm
      have hlamfac : lam * Real.sqrt lam ≤ lam ^ 2 * Real.sqrt lam :=
        mul_le_mul_of_nonneg_right hlam_sq (le_of_lt hslam)
      have hL_sq1 : (1 : ℝ) ≤ L ^ 2 := by
        have h := one_le_mul' hL1 hL1
        calc (1 : ℝ) ≤ L * L := h
          _ = L ^ 2 := (pow_two L).symm
      have hLfac : Real.sqrt L ≤ L ^ 2 * Real.sqrt L := by
        calc Real.sqrt L = 1 * Real.sqrt L := (one_mul _).symm
          _ ≤ L ^ 2 * Real.sqrt L := mul_le_mul_of_nonneg_right hL_sq1 hsL
      calc Real.sqrt L * μ₀ ^ 3 * (r : ℝ) ^ 3 * (lam * Real.sqrt lam)
          ≤ (L ^ 2 * Real.sqrt L) * (U ^ 2 * Real.sqrt U) *
            (V ^ 2 * Real.sqrt V) * (lam ^ 2 * Real.sqrt lam) := by
            have hpos1 : (0 : ℝ) ≤ μ₀ ^ 3 := by positivity
            have hpos2 : (0 : ℝ) ≤ (r : ℝ) ^ 3 := by positivity
            have hpos3 : (0 : ℝ) ≤ L ^ 2 * Real.sqrt L :=
              mul_nonneg (pow_nonneg (le_of_lt hL0) 2) hsL
            have hpos4 : (0 : ℝ) ≤ U ^ 2 * Real.sqrt U :=
              mul_nonneg (pow_nonneg (le_of_lt hU0) 2) (le_of_lt hsU)
            have hpos5 : (0 : ℝ) ≤ V ^ 2 * Real.sqrt V :=
              mul_nonneg (pow_nonneg (le_of_lt hV0) 2) (le_of_lt hsV)
            have s1 : Real.sqrt L * μ₀ ^ 3 ≤
                (L ^ 2 * Real.sqrt L) * (U ^ 2 * Real.sqrt U) :=
              mul_le_mul hLfac hUcube hpos1 hpos3
            have s2 : Real.sqrt L * μ₀ ^ 3 * (r : ℝ) ^ 3 ≤
                (L ^ 2 * Real.sqrt L) * (U ^ 2 * Real.sqrt U) *
                  (V ^ 2 * Real.sqrt V) :=
              mul_le_mul s1 hVcube hpos2 (mul_nonneg hpos3 hpos4)
            exact mul_le_mul s2 hlamfac
              (mul_nonneg (le_of_lt hlam0) (le_of_lt hslam))
              (mul_nonneg (mul_nonneg hpos3 hpos4) hpos5)
        _ = K ^ 2 * Real.sqrt K := by
            rw [hK2, hsqrtK]; ring
    -- combine
    calc spectralNorm Y
        ≤ A ^ 2 * (Cfixed * Real.sqrt (L * nR * A) *
          (Cbase * μ₀ ^ 3 * (r : ℝ) ^ 3 /
            (mnR ^ 2 * Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))))) := hchain
      _ = (Cfixed * Cbase) * (A ^ 2 * Real.sqrt (L * nR * A) *
          (μ₀ ^ 3 * (r : ℝ) ^ 3 /
            (mnR ^ 2 * Real.sqrt ((n₁ : ℝ) * (n₂ : ℝ))))) := by
          ring
      _ ≤ (Cfixed * Cbase) * Real.rpow lam (-((3 : ℝ) / 2)) :=
          mul_le_mul_of_nonneg_left hscalar
            (mul_nonneg (le_of_lt hCf) (le_of_lt hCb))
