-- Prove2me | solution 1 for quadratic_mean_response_rate_scale_absorbed_by_lambda_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-22T03:25:43.569609+00:00
-- url     : https://prove2.me/submissions/dd1a021e-898a-4f8d-ab55-8cbfc301906f

import Definitions.Def_matrix_completion_svd
import Definitions.Def_matrix_completion_tangent
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.InnerProductSpace.Basic

open scoped Classical BigOperators

open Matrix MatrixCompletion

theorem solution (Cscale : ℝ) :
    0 < Cscale →
    ∃ Cthreshold : ℝ, 0 < Cthreshold ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ → A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          lam * Real.rpow μ₀ ((4 : ℝ) / 3) *
            (↑(max n₁ n₂)) * Real.rpow (r : ℝ) ((4 : ℝ) / 3) *
              (β * Real.log (↑(max n₁ n₂))) →
        ∀ Y : Matrix (Fin n₁) (Fin n₂) ℝ,
        spectralNorm Y ≤
          Cscale * μ₀ * ((r : ℝ) / (↑(max n₁ n₂))) *
            Real.sqrt
              ((β * (↑(max n₁ n₂)) *
                  Real.log (↑(max n₁ n₂))) /
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
            entrySupNorm
              ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) •
                signMatrix S) →
        spectralNorm Y ≤
          Cthreshold * Real.rpow lam (-((3 : ℝ) / 2)) := by
  intro hCs
  ----------------------------------------------------------------
  -- HELPER A: entrySupNorm (c . X) = |c| * entrySupNorm X
  ----------------------------------------------------------------
  have entrySupNorm_smul_aux : ∀ {a b : Nat} (c : ℝ) (X : RealMatrix a b),
      entrySupNorm (c • X) = |c| * entrySupNorm X := by
    intro a b c X
    unfold entrySupNorm
    have step1 : ∀ i : Fin a, (⨆ j : Fin b, |(c • X) i j|) = |c| * ⨆ j : Fin b, |X i j| := by
      intro i
      have : (fun j : Fin b => |(c • X) i j|) = (fun j => |c| * |X i j|) := by
        funext j; simp [Matrix.smul_apply, abs_mul]
      rw [this, Real.mul_iSup_of_nonneg (abs_nonneg c)]
    rw [funext step1, Real.mul_iSup_of_nonneg (abs_nonneg c)]
  ----------------------------------------------------------------
  -- HELPER B: entrySupNorm (signMatrix) ≤ mu0 r / sqrt(n1 n2)
  ----------------------------------------------------------------
  have entrySupNorm_signMatrix_le : ∀ {n1 n2 r : Nat} {M0 : RealMatrix n1 n2}
      (S : SVD M0 r) (mu0 : ℝ), A0 S mu0 → 0 < n1 → 0 < n2 →
      entrySupNorm (signMatrix S) ≤ mu0 * (r : ℝ) / Real.sqrt ((n1 : ℝ) * (n2 : ℝ)) := by
    intro n1 n2 r M0 S mu0 h0 hn1 hn2
    haveI : Nonempty (Fin n1) := ⟨⟨0, hn1⟩⟩
    haveI : Nonempty (Fin n2) := ⟨⟨0, hn2⟩⟩
    obtain ⟨h0u, h0v⟩ := h0
    set Eu : Fin n1 → ℝ := fun i => ∑ k, (S.u k i) ^ 2 with hEu
    set Ev : Fin n2 → ℝ := fun j => ∑ k, (S.v k j) ^ 2 with hEv
    have hEu_nonneg : ∀ i, 0 ≤ Eu i := fun i => Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have hEv_nonneg : ∀ j, 0 ≤ Ev j := fun j => Finset.sum_nonneg (fun k _ => sq_nonneg _)
    have hEu_bdd : BddAbove (Set.range Eu) := Finite.bddAbove_range _
    have hEv_bdd : BddAbove (Set.range Ev) := Finite.bddAbove_range _
    have hsupu_nonneg : 0 ≤ ⨆ i, Eu i := le_ciSup_of_le hEu_bdd ⟨0, hn1⟩ (hEu_nonneg _)
    have hn1R : (0 : ℝ) < n1 := by exact_mod_cast hn1
    have hn2R : (0 : ℝ) < n2 := by exact_mod_cast hn2
    have hmu0_nonneg : 0 ≤ mu0 := by
      have hcoh_nonneg : 0 ≤ coherence n1 r S.u := by
        unfold coherence
        apply mul_nonneg (by positivity)
        simpa [hEu] using hsupu_nonneg
      linarith [h0u]
    have hmur_nonneg : 0 ≤ mu0 * (r : ℝ) := mul_nonneg hmu0_nonneg (by positivity)
    have key_u : ∀ i : Fin n1, Eu i ≤ mu0 * (r : ℝ) / (n1 : ℝ) := by
      intro i
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simp [hEu]
      · have hrR : (0 : ℝ) < r := by exact_mod_cast hr
        have hsup_le : (⨆ i, Eu i) ≤ mu0 * (r : ℝ) / (n1 : ℝ) := by
          have hcoh : (n1 : ℝ) / r * (⨆ i, Eu i) ≤ mu0 := by
            have := h0u; unfold coherence at this; simpa [hEu] using this
          rw [div_mul_eq_mul_div, div_le_iff₀ hrR] at hcoh
          rw [le_div_iff₀ hn1R]; nlinarith [hcoh]
        exact le_trans (le_ciSup hEu_bdd i) hsup_le
    have key_v : ∀ j : Fin n2, Ev j ≤ mu0 * (r : ℝ) / (n2 : ℝ) := by
      intro j
      rcases Nat.eq_zero_or_pos r with hr | hr
      · subst hr; simp [hEv]
      · have hrR : (0 : ℝ) < r := by exact_mod_cast hr
        have hsup_le : (⨆ j, Ev j) ≤ mu0 * (r : ℝ) / (n2 : ℝ) := by
          have hcoh : (n2 : ℝ) / r * (⨆ j, Ev j) ≤ mu0 := by
            have := h0v; unfold coherence at this; simpa [hEv] using this
          rw [div_mul_eq_mul_div, div_le_iff₀ hrR] at hcoh
          rw [le_div_iff₀ hn2R]; nlinarith [hcoh]
        exact le_trans (le_ciSup hEv_bdd j) hsup_le
    have entry_bound : ∀ (i : Fin n1) (j : Fin n2),
        |signMatrix S i j| ≤ mu0 * (r : ℝ) / Real.sqrt ((n1 : ℝ) * (n2 : ℝ)) := by
      intro i j
      have hsm : signMatrix S i j = ∑ k, S.u k i * S.v k j := by
        simp only [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply]
      rw [hsm]
      have hcs : (∑ k, S.u k i * S.v k j) ^ 2 ≤ Eu i * Ev j := by
        simpa [hEu, hEv] using
          (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun k => S.u k i) (fun k => S.v k j))
      have habs : |∑ k, S.u k i * S.v k j| ≤ Real.sqrt (Eu i * Ev j) := by
        rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt hcs
      have hprod_le : Eu i * Ev j ≤ (mu0 * (r : ℝ) / (n1 : ℝ)) * (mu0 * (r : ℝ) / (n2 : ℝ)) := by
        apply mul_le_mul (key_u i) (key_v j) (hEv_nonneg j); positivity
      have hsqrt_le : Real.sqrt (Eu i * Ev j)
          ≤ Real.sqrt ((mu0 * (r : ℝ) / (n1 : ℝ)) * (mu0 * (r : ℝ) / (n2 : ℝ))) :=
        Real.sqrt_le_sqrt hprod_le
      have hrhs : Real.sqrt ((mu0 * (r : ℝ) / (n1 : ℝ)) * (mu0 * (r : ℝ) / (n2 : ℝ)))
          = mu0 * (r : ℝ) / Real.sqrt ((n1 : ℝ) * (n2 : ℝ)) := by
        rw [show (mu0 * (r : ℝ) / (n1 : ℝ)) * (mu0 * (r : ℝ) / (n2 : ℝ))
              = (mu0 * (r : ℝ)) ^ 2 / ((n1 : ℝ) * (n2 : ℝ)) by ring]
        rw [Real.sqrt_div (by positivity), Real.sqrt_sq hmur_nonneg]
      rw [← hrhs]; exact le_trans habs hsqrt_le
    unfold entrySupNorm
    apply ciSup_le; intro i; apply ciSup_le; intro j; exact entry_bound i j
  ----------------------------------------------------------------
  -- HELPER C: envelope_bound (pure-real arithmetic)
  ----------------------------------------------------------------
  have envelope_bound : ∀ (beta lam mu0 K nn m esn : ℝ),
      2 < beta → 1 ≤ lam → 1 ≤ mu0 → ∀ (rr : ℝ), 1 ≤ rr → 2 ≤ K →
      0 < nn → nn ≤ K^2 → 0 < m → m ≤ nn → 0 ≤ esn → esn ≤ mu0 * rr / Real.sqrt nn →
      m ≥ lam * Real.rpow mu0 (4/3) * K * Real.rpow rr (4/3) * (beta * Real.log K) →
      Cscale * mu0 * (rr / K) * Real.sqrt ((beta * K * Real.log K) / (m / nn)) *
          ((m / nn)⁻¹ * esn)
        ≤ (Cscale / (2 * Real.log 2)) * Real.rpow lam (-(3/2)) := by
    intro beta lam mu0 K nn m esn hb hlam hmu0 rr hr hK hnn_pos hnn_le hm_pos hm_le hesn hesn_le hmbound
    have hKpos : 0 < K := by linarith
    have hrr_pos : 0 < rr := by linarith
    have hmu0_pos : 0 < mu0 := by linarith
    have hlam_pos : 0 < lam := by linarith
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hlogK_pos : 0 < Real.log K := Real.log_pos (by linarith)
    have hlogK_ge : Real.log 2 ≤ Real.log K := Real.log_le_log (by norm_num) hK
    have hbeta_pos : 0 < beta := by linarith
    set B := lam * Real.rpow mu0 (4/3) * K * Real.rpow rr (4/3) * (beta * Real.log K) with hB
    have hmu0_43_pos : 0 < Real.rpow mu0 (4/3) := Real.rpow_pos_of_pos hmu0_pos _
    have hrr_43_pos : 0 < Real.rpow rr (4/3) := Real.rpow_pos_of_pos hrr_pos _
    have hB_pos : 0 < B := by rw [hB]; positivity
    have hsqrtnn_pos : 0 < Real.sqrt nn := Real.sqrt_pos.mpr hnn_pos
    have hpref_nonneg : 0 ≤ Cscale * mu0 * (rr / K) *
        Real.sqrt ((beta * K * Real.log K) / (m / nn)) * ((m / nn)⁻¹) := by positivity
    have step1 : Cscale * mu0 * (rr / K) *
          Real.sqrt ((beta * K * Real.log K) / (m / nn)) * ((m / nn)⁻¹ * esn)
        ≤ Cscale * mu0 * (rr / K) *
          Real.sqrt ((beta * K * Real.log K) / (m / nn)) *
          ((m / nn)⁻¹ * (mu0 * rr / Real.sqrt nn)) := by
      rw [show Cscale * mu0 * (rr / K) *
            Real.sqrt ((beta * K * Real.log K) / (m / nn)) * ((m / nn)⁻¹ * esn)
          = (Cscale * mu0 * (rr / K) *
            Real.sqrt ((beta * K * Real.log K) / (m / nn)) * ((m / nn)⁻¹)) * esn by ring,
         show Cscale * mu0 * (rr / K) *
            Real.sqrt ((beta * K * Real.log K) / (m / nn)) *
            ((m / nn)⁻¹ * (mu0 * rr / Real.sqrt nn))
          = (Cscale * mu0 * (rr / K) *
            Real.sqrt ((beta * K * Real.log K) / (m / nn)) * ((m / nn)⁻¹)) *
            (mu0 * rr / Real.sqrt nn) by ring]
      exact mul_le_mul_of_nonneg_left hesn_le hpref_nonneg
    have hBm : B ≤ m := hmbound
    have hpn_pos : 0 < m / nn := by positivity
    have hBn_pos : 0 < B / nn := by positivity
    have hBn_le : B / nn ≤ m / nn := by gcongr
    have step2 : Cscale * mu0 * (rr / K) *
          Real.sqrt ((beta * K * Real.log K) / (m / nn)) *
          ((m / nn)⁻¹ * (mu0 * rr / Real.sqrt nn))
        ≤ Cscale * mu0 * (rr / K) *
          Real.sqrt ((beta * K * Real.log K) / (B / nn)) *
          ((B / nn)⁻¹ * (mu0 * rr / Real.sqrt nn)) := by
      have hDpos : 0 ≤ beta * K * Real.log K := by positivity
      gcongr Cscale * mu0 * (rr / K) * Real.sqrt ?_ * (?_ * (mu0 * rr / Real.sqrt nn))
      · gcongr
      · exact inv_anti₀ hBn_pos hBn_le
    have step3 : Cscale * mu0 * (rr / K) *
          Real.sqrt ((beta * K * Real.log K) / (B / nn)) *
          ((B / nn)⁻¹ * (mu0 * rr / Real.sqrt nn))
        = Cscale * (nn / K^2) * (1 / (beta * Real.log K)) * Real.rpow lam (-(3/2)) := by
      rw [hB]
      set a := mu0 ^ ((1:ℝ)/3) with ha
      set c := rr ^ ((1:ℝ)/3) with hc
      set s := lam ^ ((1:ℝ)/2) with hs
      have ha_pos : 0 < a := Real.rpow_pos_of_pos hmu0_pos _
      have hc_pos : 0 < c := Real.rpow_pos_of_pos hrr_pos _
      have hs_pos : 0 < s := Real.rpow_pos_of_pos hlam_pos _
      have hmu0_eq : mu0 = a^(3:ℕ) := by
        rw [ha, ← Real.rpow_natCast (mu0 ^ ((1:ℝ)/3)) 3, ← Real.rpow_mul hmu0_pos.le]; norm_num
      have hrr_eq : rr = c^(3:ℕ) := by
        rw [hc, ← Real.rpow_natCast (rr ^ ((1:ℝ)/3)) 3, ← Real.rpow_mul hrr_pos.le]; norm_num
      have hlam_eq : lam = s^(2:ℕ) := by
        rw [hs, ← Real.rpow_natCast (lam ^ ((1:ℝ)/2)) 2, ← Real.rpow_mul hlam_pos.le]; norm_num
      have hmu0_43 : Real.rpow mu0 (4/3) = a^(4:ℕ) := by
        rw [ha, ← Real.rpow_natCast (mu0 ^ ((1:ℝ)/3)) 4, ← Real.rpow_mul hmu0_pos.le]
        show mu0 ^ ((4:ℝ)/3) = _; congr 1; norm_num
      have hrr_43 : Real.rpow rr (4/3) = c^(4:ℕ) := by
        rw [hc, ← Real.rpow_natCast (rr ^ ((1:ℝ)/3)) 4, ← Real.rpow_mul hrr_pos.le]
        show rr ^ ((4:ℝ)/3) = _; congr 1; norm_num
      have hlam_m32 : Real.rpow lam (-(3/2)) = (s^(3:ℕ))⁻¹ := by
        rw [hs, ← Real.rpow_natCast (lam ^ ((1:ℝ)/2)) 3, ← Real.rpow_mul hlam_pos.le,
          ← Real.rpow_neg hlam_pos.le]
        show lam ^ (-(3/2):ℝ) = _; congr 1; push_cast; ring
      rw [hmu0_43, hrr_43, hlam_m32, hmu0_eq, hrr_eq, hlam_eq]
      have hrad_pos : 0 ≤ (beta * K * Real.log K) /
          ((s^(2:ℕ) * a^(4:ℕ) * K * c^(4:ℕ) * (beta * Real.log K)) / nn) := by positivity
      have hLHS_nonneg : 0 ≤ Cscale * a^(3:ℕ) * (c^(3:ℕ) / K) *
            Real.sqrt ((beta * K * Real.log K) /
              ((s^(2:ℕ) * a^(4:ℕ) * K * c^(4:ℕ) * (beta * Real.log K)) / nn)) *
            (((s^(2:ℕ) * a^(4:ℕ) * K * c^(4:ℕ) * (beta * Real.log K)) / nn)⁻¹ *
              (a^(3:ℕ) * c^(3:ℕ) / Real.sqrt nn)) := by positivity
      have hRHS_nonneg : 0 ≤ Cscale * (nn / K^2) * (1 / (beta * Real.log K)) * (s^(3:ℕ))⁻¹ := by
        positivity
      rw [← pow_left_inj₀ hLHS_nonneg hRHS_nonneg (n := 2) (by norm_num)]
      simp only [mul_pow, div_pow]
      rw [Real.sq_sqrt hrad_pos, Real.sq_sqrt hnn_pos.le]
      field_simp
    have step4 : Cscale * (nn / K^2) * (1 / (beta * Real.log K)) * Real.rpow lam (-(3/2))
        ≤ (Cscale / (2 * Real.log 2)) * Real.rpow lam (-(3/2)) := by
      have hlam_m32_nonneg : 0 ≤ Real.rpow lam (-(3/2)) := Real.rpow_nonneg hlam_pos.le _
      have hnnK : nn / K^2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hnn_le
      have hlogbound : 1 / (beta * Real.log K) ≤ 1 / (2 * Real.log 2) := by
        apply one_div_le_one_div_of_le
        · positivity
        · nlinarith [hlog2, hlogK_ge]
      have hkey : Cscale * (nn / K^2) * (1 / (beta * Real.log K)) ≤ Cscale / (2 * Real.log 2) := by
        calc Cscale * (nn / K^2) * (1 / (beta * Real.log K))
            ≤ Cscale * 1 * (1 / (2 * Real.log 2)) := by gcongr
          _ = Cscale / (2 * Real.log 2) := by ring
      exact mul_le_mul_of_nonneg_right hkey hlam_m32_nonneg
    calc Cscale * mu0 * (rr / K) *
          Real.sqrt ((beta * K * Real.log K) / (m / nn)) * ((m / nn)⁻¹ * esn)
        ≤ _ := step1
      _ ≤ _ := step2
      _ = _ := step3
      _ ≤ _ := step4
  ----------------------------------------------------------------
  -- MAIN
  ----------------------------------------------------------------
  refine ⟨Cscale / (2 * Real.log 2), ?_, ?_⟩
  · have : 0 < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  intro β lam hβ hlam n₁ n₂ r m M μ₀ μ₁ S hn1 hn2 hr hm hμ0 hμ1 hA0 hA1 hmbnd Y hY
  set K : ℝ := (↑(max n₁ n₂) : ℝ) with hKdef
  have hRHS_nonneg : 0 ≤ Cscale / (2 * Real.log 2) * Real.rpow lam (-((3:ℝ)/2)) := by
    have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have : 0 ≤ Real.rpow lam (-((3:ℝ)/2)) := Real.rpow_nonneg (by linarith) _
    positivity
  -- Edge: max n₁ n₂ = 1  (⟺ n₁ = n₂ = 1)
  rcases Nat.lt_or_ge (max n₁ n₂) 2 with hmaxlt | hmaxge
  · -- max < 2 and max ≥ 1, so max = 1, n₁=n₂=1, log K = 0 ⟹ given_bound = 0.
    have hmax1 : max n₁ n₂ = 1 := by
      have : 1 ≤ max n₁ n₂ := le_max_of_le_left hn1
      omega
    have hK1 : K = 1 := by rw [hKdef, hmax1]; norm_num
    have hlogK0 : Real.log K = 0 := by rw [hK1]; exact Real.log_one
    -- the sqrt term has numerator β * K * log K = 0
    have hY0 : spectralNorm Y ≤ 0 := by
      refine le_trans hY ?_
      rw [show (β * (↑(max n₁ n₂)) * Real.log (↑(max n₁ n₂)))
            = (β * K * Real.log K) from by rw [hKdef]]
      rw [hlogK0, mul_zero, zero_div, Real.sqrt_zero, mul_zero, zero_mul]
    have hYnn : 0 ≤ spectralNorm Y := by
      unfold spectralNorm; exact norm_nonneg _
    have : spectralNorm Y = 0 := le_antisymm hY0 hYnn
    rw [this]; exact hRHS_nonneg
  · -- main regime: max ≥ 2
    have hK2 : 2 ≤ K := by rw [hKdef]; exact_mod_cast hmaxge
    -- Edge: m = 0
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0
      -- p = 0, p⁻¹ = 0, entrySupNorm(0 . sign) = 0 ⟹ given_bound = 0
      have hY0 : spectralNorm Y ≤ 0 := by
        refine le_trans hY ?_
        have hp0 : ((0:ℕ):ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) = 0 := by simp
        have hesn0 : entrySupNorm ((((0:ℕ) : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ • signMatrix S) = 0 := by
          rw [hp0, _root_.inv_zero, zero_smul]
          rw [show (0 : RealMatrix n₁ n₂) = (0:ℝ) • signMatrix S from (zero_smul _ _).symm,
            entrySupNorm_smul_aux (0:ℝ) (signMatrix S), abs_zero, zero_mul]
        rw [hesn0, mul_zero]
      have hYnn : 0 ≤ spectralNorm Y := by unfold spectralNorm; exact norm_nonneg _
      rw [le_antisymm hY0 hYnn]; exact hRHS_nonneg
    · -- m ≥ 1
      have hmR_pos : (0:ℝ) < (m:ℝ) := by exact_mod_cast hmpos
      have hnn_pos : (0:ℝ) < (n₁:ℝ)*(n₂:ℝ) := by positivity
      -- nn ≤ K^2
      have hnn_le : (n₁:ℝ)*(n₂:ℝ) ≤ K^2 := by
        rw [hKdef]
        have h1 : (n₁:ℝ) ≤ (↑(max n₁ n₂):ℝ) := by exact_mod_cast Nat.le_max_left n₁ n₂
        have h2 : (n₂:ℝ) ≤ (↑(max n₁ n₂):ℝ) := by exact_mod_cast Nat.le_max_right n₁ n₂
        nlinarith [Nat.cast_nonneg (α := ℝ) n₁, Nat.cast_nonneg (α := ℝ) n₂,
          Nat.cast_nonneg (α := ℝ) (max n₁ n₂)]
      have hm_le : (m:ℝ) ≤ (n₁:ℝ)*(n₂:ℝ) := by
        rw [← Nat.cast_mul]; exact_mod_cast hm
      have hrr1 : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
      -- entrySupNorm(sign) bound
      have hesn_le : entrySupNorm (signMatrix S)
          ≤ μ₀ * (r:ℝ) / Real.sqrt ((n₁:ℝ)*(n₂:ℝ)) :=
        entrySupNorm_signMatrix_le S μ₀ hA0 hn1 hn2
      have hesn_nn : 0 ≤ entrySupNorm (signMatrix S) := by
        unfold entrySupNorm
        haveI : Nonempty (Fin n₁) := ⟨⟨0, hn1⟩⟩
        haveI : Nonempty (Fin n₂) := ⟨⟨0, hn2⟩⟩
        refine le_ciSup_of_le (Finite.bddAbove_range _) ⟨0, hn1⟩ ?_
        refine le_ciSup_of_le (Finite.bddAbove_range _) ⟨0, hn2⟩ ?_
        exact abs_nonneg _
      -- p ≥ 0
      have hp_nonneg : 0 ≤ (m:ℝ) / ((n₁:ℝ)*(n₂:ℝ)) := by positivity
      -- rewrite entrySupNorm(p⁻¹ . sign) = p⁻¹ * entrySupNorm sign
      have hrw : entrySupNorm ((((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹) • signMatrix S)
          = ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ * entrySupNorm (signMatrix S) := by
        rw [entrySupNorm_smul_aux, abs_of_nonneg (by positivity)]
      -- assemble: given_bound = envelope LHS
      refine le_trans hY ?_
      rw [hrw]
      -- now match the form to envelope_bound
      have hmatch :
          Cscale * μ₀ * ((r : ℝ) / K) *
            Real.sqrt ((β * K * Real.log K) /
              ((m:ℝ)/((n₁:ℝ)*(n₂:ℝ)))) *
            (((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))⁻¹ * entrySupNorm (signMatrix S))
          ≤ (Cscale / (2 * Real.log 2)) * Real.rpow lam (-((3:ℝ)/2)) := by
        have := envelope_bound β lam μ₀ K ((n₁:ℝ)*(n₂:ℝ)) (m:ℝ)
          (entrySupNorm (signMatrix S)) hβ hlam hμ0 (r:ℝ) hrr1 hK2
          hnn_pos hnn_le hmR_pos hm_le hesn_nn hesn_le ?_
        · -- the conclusion: need (-(3/2)) = (-((3:ℝ)/2)) match
          convert this using 3
        · -- hmbound for envelope (with K and casts)
          rw [hKdef]
          calc (m:ℝ) ≥ lam * Real.rpow μ₀ ((4:ℝ)/3) * (↑(max n₁ n₂))
                * Real.rpow (r:ℝ) ((4:ℝ)/3) * (β * Real.log (↑(max n₁ n₂))) := hmbnd
            _ = lam * Real.rpow μ₀ (4/3) * (↑(max n₁ n₂)) * Real.rpow (r:ℝ) (4/3)
                * (β * Real.log (↑(max n₁ n₂))) := by norm_num
      -- bridge the K notation in the goal
      rw [hKdef] at hmatch ⊢
      convert hmatch using 2
