-- Prove2me | solution 1 for neumann_certificate_remainder_formula_bound_from_general_bound
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T22:51:54.217857+00:00
-- url     : https://prove2.me/submissions/4c577309-2f1b-4c8e-80e1-e2c97e563484

import Definitions.Def_matrix_completion_neumann
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
Solution for node 667563fb
`neumann_certificate_remainder_formula_bound_from_general_bound`.

CR2009 (Candes-Recht, Exact matrix completion via convex optimization),
Lemma 4.8 constant absorption with k0 = 3 (Section 4.3 / Section 6.3):
the general Theorem 1.3 sample lower bound forces BOTH the Lemma-4.8 density
hypothesis  m >= CR*mu0*n*r*beta*log n  AND the numerical estimate that the
explicit remainder formula is at most 1/2.

Witness C = |CR| + sqrt(2|Ctail|) + 1.  Pure real-analysis (no probability,
no SVD geometry).  Self-contained on Def_matrix_completion_neumann + Mathlib.
-/

namespace MatrixCompletion

open scoped Classical BigOperators
open Real

set_option maxHeartbeats 4000000 in
theorem node_667563fb (CR Ctail : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        (m : ℝ) ≥
            CR * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) ∧
          neumannRemainderFormulaBound Ctail β μ₀ (max n₁ n₂) r m ≤
            (1 : ℝ) / 2 := by
  refine ⟨|CR| + Real.sqrt (2 * |Ctail|) + 1, ?_, ?_⟩
  · have h1 : 0 ≤ |CR| := abs_nonneg _
    have h2 : 0 ≤ Real.sqrt (2 * |Ctail|) := Real.sqrt_nonneg _
    linarith
  intro C' hC' β hβ n₁ n₂ r m M μ₀ μ₁ S hn₁ hn₂ hr hcard hμ₀ hμ₁ hA0 hA1 hLHS
  set n : ℕ := max n₁ n₂ with hn
  have hnR : (1:ℝ) ≤ (n:ℝ) := by
    have : 1 ≤ n := le_trans hn₁ (le_max_left _ _)
    exact_mod_cast this
  have hrR : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hμ₀0 : (0:ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hCR_le : CR ≤ |CR| + Real.sqrt (2 * |Ctail|) + 1 := by
    have h1 : CR ≤ |CR| := le_abs_self _
    have h2 : 0 ≤ Real.sqrt (2 * |Ctail|) := Real.sqrt_nonneg _
    linarith
  have hC'pos : 0 < C' := by
    have h1 : 0 ≤ |CR| := abs_nonneg _
    have h2 : 0 ≤ Real.sqrt (2 * |Ctail|) := Real.sqrt_nonneg _
    have : (0:ℝ) < |CR| + Real.sqrt (2 * |Ctail|) + 1 := by linarith
    linarith [le_trans (le_of_lt this) hC']
  -- The MAX
  set MAXv : ℝ := max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4)) with hMAXv
  have hβ0 : (0:ℝ) < β := by linarith
  -- abbreviations
  set t : ℝ := Real.rpow (n:ℝ) ((1:ℝ)/4) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos (by linarith) _
  have hcast_eq : (↑(max n₁ n₂):ℝ) = (n:ℝ) := rfl
  -- MAX ≥ μ₀ * t
  have hMAXge : MAXv ≥ μ₀ * t := by
    rw [hMAXv]
    exact le_max_right _ _
  -- log handling: case n = 1
  by_cases hn1 : (n:ℝ) = 1
  · -- log n = 0 ⇒ both RHS are 0 / remainder = 0
    have hlog0 : Real.log (n:ℝ) = 0 := by rw [hn1]; exact Real.log_one
    constructor
    · rw [hcast_eq, hlog0]
      have : CR * μ₀ * (n:ℝ) * (r:ℝ) * (β * 0) = 0 := by ring
      rw [this]; positivity
    · -- remainder: the rpow factor has log n = 0 in numerator
      unfold neumannRemainderFormulaBound
      rw [hcast_eq, hlog0]
      -- (μ0*n*r*(β*0))/m = 0
      have hz : (μ₀ * (n:ℝ) * (r:ℝ) * (β * 0)) / (m:ℝ) = 0 := by ring_nf
      rw [hz]
      have hzr : Real.rpow 0 ((3:ℝ)/2) = 0 := Real.zero_rpow (by norm_num)
      rw [hzr]
      simp only [mul_zero]
      norm_num
  · -- n ≥ 2
    have hngt1 : (1:ℝ) < (n:ℝ) := lt_of_le_of_ne hnR (Ne.symm hn1)
    have hlogpos : 0 < Real.log (n:ℝ) := Real.log_pos hngt1
    have hn2nat : 2 ≤ n := by
      have h1n : 1 < n := by exact_mod_cast hngt1
      omega
    have hn2 : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2nat
    set P : ℝ := β * Real.log (n:ℝ) with hP
    have hP0 : 0 < P := by rw [hP]; positivity
    have hPge1 : (1:ℝ) ≤ P := by
      -- β > 2, log n ≥ log 2 > 1/2 ⇒ β log n > 2·(1/2) = 1
      have hlog2le : Real.log 2 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) hn2
      have hl2 : (1:ℝ)/2 < Real.log 2 := by
        rw [Real.lt_log_iff_exp_lt (by norm_num)]
        have h1 : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
        have hpos : 0 < Real.exp ((1:ℝ)/2) := Real.exp_pos _
        have hsq : (Real.exp ((1:ℝ)/2))^2 = Real.exp 1 := by
          rw [← Real.exp_nat_mul]; norm_num
        nlinarith [hsq, h1, hpos]
      rw [hP]
      nlinarith [hlog2le, hl2, le_of_lt hβ0, hβ]
    set L : ℝ := μ₀ * (n:ℝ) * (r:ℝ) * P with hL
    have hL0 : 0 < L := by rw [hL]; positivity
    -- density: m ≥ C' * MAXv * n * r * P,  with MAXv ≥ μ0 t
    have hLHS' : (m:ℝ) ≥ C' * MAXv * (n:ℝ) * (r:ℝ) * P := by
      rw [hcast_eq] at hLHS
      rw [hMAXv, hP] at *
      exact hLHS
    -- core density consequence:  m ≥ C' * t * L
    have hmpos : 0 < (m:ℝ) := by
      -- m ≥ C' MAXv n r P > 0 since all factors positive (MAXv ≥ μ0 t > 0)
      have hMAXpos : 0 < MAXv := lt_of_lt_of_le (by positivity) hMAXge
      have hnpos : (0:ℝ) < (n:ℝ) := by linarith
      have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
      have : 0 < C' * MAXv * (n:ℝ) * (r:ℝ) * P := by positivity
      linarith
    have hmL : (m:ℝ) ≥ C' * t * L := by
      have hnpos : (0:ℝ) < (n:ℝ) := by linarith
      have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
      have hstep : C' * (μ₀ * t) * (n:ℝ) * (r:ℝ) * P ≤ C' * MAXv * (n:ℝ) * (r:ℝ) * P := by
        have hfac : 0 ≤ C' * (n:ℝ) * (r:ℝ) * P := by positivity
        nlinarith [mul_le_mul_of_nonneg_left hMAXge (le_of_lt hC'pos), hfac, hnpos, hrpos, hP0, ht0]
      have heq : C' * (μ₀ * t) * (n:ℝ) * (r:ℝ) * P = C' * t * L := by rw [hL]; ring
      rw [heq] at hstep
      linarith [hLHS', hstep]
    -- ===== Part (i):  m ≥ CR μ₀ n r P =====
    refine ⟨?_, ?_⟩
    · rw [hcast_eq]
      -- m ≥ C' t L ≥ C' μ0 n r P ≥ CR μ0 n r P   (t ≥ 1, C' ≥ CR; or CR ≤ 0 trivial)
      have htge1 : (1:ℝ) ≤ t := by
        rw [ht]; exact Real.one_le_rpow hnR (by norm_num)
      have hnpos : (0:ℝ) < (n:ℝ) := by linarith
      have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
      -- C' t L ≥ C' L = C' μ0 n r P
      have h1 : C' * t * L ≥ C' * L := by
        have : 0 ≤ C' * L * (t - 1) := by
          apply mul_nonneg (by positivity)
          linarith [htge1]
        nlinarith [this]
      have h2 : C' * L = C' * μ₀ * (n:ℝ) * (r:ℝ) * P := by rw [hL]; ring
      have h3 : C' * μ₀ * (n:ℝ) * (r:ℝ) * P ≥ CR * μ₀ * (n:ℝ) * (r:ℝ) * P := by
        have hCRle : CR ≤ C' := le_trans hCR_le hC'
        have hfac : 0 ≤ μ₀ * (n:ℝ) * (r:ℝ) * P := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hCRle hfac]
      linarith [hmL, h1, h2, h3]
    -- ===== Part (ii):  remainder ≤ 1/2 =====
    · unfold neumannRemainderFormulaBound
      rw [hcast_eq]
      -- remainder = Ctail * √Aarg * Larg^(3/2),  Aarg = n²r/m, Larg = L/m
      set Larg : ℝ := (μ₀ * (n:ℝ) * (r:ℝ) * P) / (m:ℝ) with hLarg
      set Aarg : ℝ := (n:ℝ) ^ 2 * (r:ℝ) / (m:ℝ) with hAarg
      have hAarg0 : 0 ≤ Aarg := by rw [hAarg]; positivity
      have hLarg0 : 0 ≤ Larg := by rw [hLarg]; positivity
      have hnpos : (0:ℝ) < (n:ℝ) := by linarith
      have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
      -- name the remainder R = Ctail * √Aarg * Larg^(3/2)
      set R : ℝ := Ctail * Real.sqrt Aarg * Real.rpow Larg ((3:ℝ)/2) with hR
      -- t^4 = n
      have ht4 : t ^ (4:ℕ) = (n:ℝ) := by
        rw [ht]
        rw [show Real.rpow (n:ℝ) ((1:ℝ)/4) = (n:ℝ) ^ ((1:ℝ)/4) from rfl]
        rw [← Real.rpow_natCast ((n:ℝ) ^ ((1:ℝ)/4)) 4, ← Real.rpow_mul (by linarith : (0:ℝ) ≤ (n:ℝ))]
        norm_num
      -- KEY:  Aarg * Larg^3 ≤ 1/(P * C'^4)
      --   via cross-mult:  (Aarg*Larg^3) * (P*C'^4) ≤ 1, equivalently
      --   n²r·L³·P·C'⁴ ≤ m⁴   using m ≥ C'·t·L, L = μ0 n r P, t⁴ = n, μ0 ≥ 1.
      have hL0' : 0 < L := hL0
      have hmL4 : (C' * t * L)^(4:ℕ) ≤ (m:ℝ)^(4:ℕ) := by
        apply pow_le_pow_left₀ (by positivity) hmL
      -- expand: Aarg*Larg^3 = (n²r/m)*(L/m)^3 = n²r·L³/m⁴
      have hALeq : Aarg * Larg ^ (3:ℕ) = ((n:ℝ)^2 * (r:ℝ) * L^(3:ℕ)) / (m:ℝ)^(4:ℕ) := by
        rw [hAarg, hLarg, ← hL]
        field_simp
      -- bound numerator·(P C'⁴) ≤ m⁴
      have hkey : Aarg * Larg ^ (3:ℕ) * (P * C'^(4:ℕ)) ≤ 1 := by
        rw [hALeq]
        rw [div_mul_eq_mul_div, div_le_one (by positivity)]
        -- (n²r·L³)·(P·C'⁴) ≤ m⁴.   Use m⁴ ≥ (C't L)⁴ = C'⁴ t⁴ L⁴ = C'⁴ n L⁴
        -- and L = μ0 n r P ≥ n r P  ⇒ n²r ≤ n·L/P ⇒ n²r·L³·P ≤ n·L⁴
        -- ⇒ n²r·L³·P·C'⁴ ≤ C'⁴ n L⁴ ≤ m⁴.
        have hexp : (C' * t * L)^(4:ℕ) = C'^(4:ℕ) * (n:ℝ) * L^(4:ℕ) := by
          have : (C' * t * L)^(4:ℕ) = C'^(4:ℕ) * t^(4:ℕ) * L^(4:ℕ) := by ring
          rw [this, ht4]
        have hLge : L ≥ (n:ℝ) * (r:ℝ) * P := by
          rw [hL]; nlinarith [hμ₀, hnpos, hrpos, hP0]
        -- n²r·L³·P·C'⁴ ≤ C'⁴ n L⁴
        have hstep1 : (n:ℝ)^2 * (r:ℝ) * L^(3:ℕ) * (P * C'^(4:ℕ)) ≤ C'^(4:ℕ) * (n:ℝ) * L^(4:ℕ) := by
          -- divide both: need n²r·P ≤ n·L  i.e.  n·r·P ≤ L  (× n), holds by hLge
          have hbase : (n:ℝ) * (r:ℝ) * P ≤ L := hLge
          have hmul : (n:ℝ) * ((n:ℝ) * (r:ℝ) * P) ≤ (n:ℝ) * L :=
            mul_le_mul_of_nonneg_left hbase (le_of_lt hnpos)
          -- (n²r·P) ≤ n·L ; multiply by L³·C'⁴ ≥ 0
          have hfac : 0 ≤ L^(3:ℕ) * C'^(4:ℕ) := by positivity
          nlinarith [mul_le_mul_of_nonneg_right hmul hfac, hL0', hC'pos, hnpos]
        have hstep2 : C'^(4:ℕ) * (n:ℝ) * L^(4:ℕ) ≤ (m:ℝ)^(4:ℕ) := by
          rw [← hexp]; exact hmL4
        calc (n:ℝ)^2 * (r:ℝ) * L^(3:ℕ) * (P * C'^(4:ℕ))
            ≤ C'^(4:ℕ) * (n:ℝ) * L^(4:ℕ) := hstep1
          _ ≤ (m:ℝ)^(4:ℕ) := hstep2
      -- Now turn into Aarg*Larg^3 ≤ 1/(P C'^4)
      have hPC4pos : 0 < P * C'^(4:ℕ) := by positivity
      have hAL_bd : Aarg * Larg ^ (3:ℕ) ≤ 1 / (P * C'^(4:ℕ)) := by
        rw [le_div_iff₀ hPC4pos]; exact hkey
      -- R ≥ 0 case split on Ctail
      rcases le_or_gt Ctail 0 with hCt | hCt
      · -- Ctail ≤ 0 ⇒ R ≤ 0 ≤ 1/2
        have : R ≤ 0 := by
          rw [hR]
          have h1 : 0 ≤ Real.sqrt Aarg * Real.rpow Larg ((3:ℝ)/2) := by
            apply mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hLarg0 _)
          nlinarith [mul_nonpos_of_nonpos_of_nonneg hCt h1]
        linarith
      · -- Ctail > 0 ⇒ R ≥ 0 and R² ≤ 1/4
        have hRnn : 0 ≤ R := by
          rw [hR]
          apply mul_nonneg (mul_nonneg (le_of_lt hCt) (Real.sqrt_nonneg _))
            (Real.rpow_nonneg hLarg0 _)
        -- R² = Ctail² * Aarg * Larg^3
        have hRsq : R^(2:ℕ) = Ctail^(2:ℕ) * (Aarg * Larg ^ (3:ℕ)) := by
          rw [hR]
          have hsq : (Real.sqrt Aarg)^(2:ℕ) = Aarg := Real.sq_sqrt hAarg0
          have hrp : (Real.rpow Larg ((3:ℝ)/2))^(2:ℕ) = Larg ^ (3:ℕ) := by
            rw [← Real.rpow_natCast (Real.rpow Larg ((3:ℝ)/2)) 2]
            rw [show Real.rpow Larg ((3:ℝ)/2) = Larg ^ ((3:ℝ)/2) from rfl]
            rw [← Real.rpow_mul hLarg0]
            norm_num
          calc (Ctail * Real.sqrt Aarg * Real.rpow Larg ((3:ℝ)/2))^(2:ℕ)
              = Ctail^(2:ℕ) * (Real.sqrt Aarg)^(2:ℕ) * (Real.rpow Larg ((3:ℝ)/2))^(2:ℕ) := by ring
            _ = Ctail^(2:ℕ) * Aarg * Larg ^ (3:ℕ) := by rw [hsq, hrp]
            _ = Ctail^(2:ℕ) * (Aarg * Larg ^ (3:ℕ)) := by ring
        -- R² ≤ Ctail²/(P C'^4) ≤ Ctail²/C'^4 ≤ 1/4
        have hRsq_bd : R^(2:ℕ) ≤ Ctail^(2:ℕ) / (P * C'^(4:ℕ)) := by
          rw [hRsq]
          have hstep : Ctail^(2:ℕ) * (Aarg * Larg ^ (3:ℕ)) ≤ Ctail^(2:ℕ) * (1 / (P * C'^(4:ℕ))) :=
            mul_le_mul_of_nonneg_left hAL_bd (by positivity)
          calc Ctail^(2:ℕ) * (Aarg * Larg ^ (3:ℕ))
              ≤ Ctail^(2:ℕ) * (1 / (P * C'^(4:ℕ))) := hstep
            _ = Ctail^(2:ℕ) / (P * C'^(4:ℕ)) := by ring
        -- Ctail²/(P C'⁴) ≤ 1/4 :  P ≥ 1, C'⁴ ≥ 4 Ctail²
        have hC'4ge : 4 * Ctail^(2:ℕ) ≤ C'^(4:ℕ) := by
          -- C' ≥ √(2|Ctail|) so C'² ≥ 2|Ctail| ≥ 2 Ctail; and Ctail>0 ⇒ |Ctail|=Ctail
          have hCtabs : |Ctail| = Ctail := abs_of_pos hCt
          have hsq2 : (Real.sqrt (2 * |Ctail|))^(2:ℕ) = 2 * |Ctail| := by
            rw [Real.sq_sqrt (by positivity)]
          have hC'ge : Real.sqrt (2 * |Ctail|) ≤ C' := by
            have : Real.sqrt (2 * |Ctail|) ≤ |CR| + Real.sqrt (2 * |Ctail|) + 1 := by
              have := abs_nonneg CR; linarith
            linarith [le_trans this hC']
          have hsqnn : 0 ≤ Real.sqrt (2 * |Ctail|) := Real.sqrt_nonneg _
          -- C'² ≥ (√(2|Ctail|))² = 2|Ctail| = 2 Ctail
          have hC'sq : (2:ℝ) * Ctail ≤ C'^(2:ℕ) := by
            have h1 : (Real.sqrt (2 * |Ctail|))^(2:ℕ) ≤ C'^(2:ℕ) :=
              pow_le_pow_left₀ hsqnn hC'ge 2
            rw [hsq2, hCtabs] at h1; exact h1
          -- C'⁴ = (C'²)² ≥ (2 Ctail)² = 4 Ctail²
          have hsq4 : C'^(4:ℕ) = (C'^(2:ℕ))^(2:ℕ) := by ring
          have h2Ctnn : 0 ≤ (2:ℝ) * Ctail := by positivity
          have : ((2:ℝ)*Ctail)^(2:ℕ) ≤ (C'^(2:ℕ))^(2:ℕ) :=
            pow_le_pow_left₀ h2Ctnn hC'sq 2
          rw [hsq4]
          nlinarith [this]
        have hfinal : Ctail^(2:ℕ) / (P * C'^(4:ℕ)) ≤ 1/4 := by
          rw [div_le_iff₀ hPC4pos]
          -- Ctail² ≤ (1/4)·P·C'⁴.  P≥1, C'⁴≥4Ctail² ⇒ (1/4)PC'⁴ ≥ (1/4)·1·4Ctail² = Ctail²
          have hCt2nn : 0 ≤ Ctail^(2:ℕ) := by positivity
          nlinarith [hC'4ge, hPge1, mul_le_mul hPge1 hC'4ge (by positivity) hP0.le, hCt2nn]
        -- conclude R ≤ 1/2 from R≥0, R²≤1/4
        have hR2 : R^(2:ℕ) ≤ (1/2:ℝ)^(2:ℕ) := by
          have : R^(2:ℕ) ≤ 1/4 := le_trans hRsq_bd hfinal
          nlinarith [this]
        nlinarith [hR2, hRnn, sq_nonneg (R - 1/2)]


end MatrixCompletion

open MatrixCompletion

theorem solution (CR Ctail : ℝ) :
    ∃ C : ℝ, 0 < C ∧
      ∀ C' : ℝ, C ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) * (β * Real.log (↑(max n₁ n₂))) →
        (m : ℝ) ≥
            CR * μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) ∧
          neumannRemainderFormulaBound Ctail β μ₀ (max n₁ n₂) r m ≤
            (1 : ℝ) / 2 :=
  MatrixCompletion.node_667563fb CR Ctail
