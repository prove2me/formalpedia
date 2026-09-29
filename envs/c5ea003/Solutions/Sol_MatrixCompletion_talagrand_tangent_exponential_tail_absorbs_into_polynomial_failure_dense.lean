-- Prove2me | solution 1 for MatrixCompletion.talagrand_tangent_exponential_tail_absorbs_into_polynomial_failure_dense
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-22T06:16:59.520826+00:00
-- url     : https://prove2.me/submissions/0addfbba-080d-47df-8dfa-703c18d62240

import Definitions.Def_matrix_completion_talagrand
open MatrixCompletion

theorem solution
    (K Cexpect : ℝ) :
    0 < K → 0 < Cexpect →
    ∃ Ctail c : ℝ, 0 < Ctail ∧ 0 < c ∧
      ∀ (β μ₀ : ℝ) (n r m : ℕ),
        2 < β → 1 ≤ μ₀ → 0 < n → 0 < r → 0 < m →
        (m : ℝ) ≥ μ₀ * (r : ℝ) * β * (n : ℝ) * Real.log (n : ℝ) →
        3 * Real.exp
            (-(tangentSamplingDeviationScale Ctail β μ₀ n r m /
                (K * (2 * μ₀ * (n : ℝ) * (r : ℝ) / (m : ℝ)))) *
              Real.log
                (1 +
                  (2 * μ₀ * (n : ℝ) * (r : ℝ) / (m : ℝ)) *
                      tangentSamplingDeviationScale Ctail β μ₀ n r m /
                    ((2 * μ₀ * (n : ℝ) * (r : ℝ) / (m : ℝ)) +
                      (2 * μ₀ * (n : ℝ) * (r : ℝ) / (m : ℝ)) *
                        tangentSamplingDeviationScale Cexpect β μ₀ n r m))) ≤
          c * Real.rpow (n : ℝ) (-β) := by
  intro hK hCexpect
  have crux_E_ge
      (K Cexpect Ctail Se a u t : ℝ)
      (hK : 0 < K) (hCexpect : 0 < Cexpect) (hlog2 : 0 < Real.log 2)
      (ht0 : 0 < t) (ha0 : 0 ≤ a) (hu0 : 0 ≤ u)
      (h1Se : 0 < 1 + Se) (h1u : 0 < 1 + u)
      (hSele : 1 + Se ≤ 1 + Cexpect)
      (hBoundA : Ctail * t / (2 * K) ≤ a)
      (hau : a * u = Ctail ^ 2 * t / (2 * K * (1 + Se)))
      (hCt1 : 2 * K / Real.log 2 ≤ Ctail)
      (hCt2 : Real.sqrt (4 * (1 + Cexpect) * K) ≤ Ctail) :
      t ≤ a * Real.log (1 + u) := by
    by_cases hcase : 1 ≤ u
    · -- u ≥ 1
      have hlog : Real.log 2 ≤ Real.log (1 + u) :=
        Real.log_le_log (by norm_num) (by linarith)
      have h1 : a * Real.log 2 ≤ a * Real.log (1 + u) :=
        mul_le_mul_of_nonneg_left hlog ha0
      have hCl : 2 * K ≤ Ctail * Real.log 2 := by
        have h := hCt1
        rw [div_le_iff₀ hlog2] at h; linarith
      have h2 : t ≤ (Ctail * t / (2 * K)) * Real.log 2 := by
        rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0:ℝ) < 2 * K)]
        nlinarith [hCl, ht0]
      have h3 : (Ctail * t / (2 * K)) * Real.log 2 ≤ a * Real.log 2 :=
        mul_le_mul_of_nonneg_right hBoundA (le_of_lt hlog2)
      linarith
    · -- u < 1
      have hcase : u < 1 := not_le.mp hcase
      have hule1 : u ≤ 1 := le_of_lt hcase
      have hloglb : u / (1 + u) ≤ Real.log (1 + u) := by
        have hl := Real.one_sub_inv_le_log_of_pos h1u
        have hne : (1 + u) ≠ 0 := ne_of_gt h1u
        have heq : 1 - (1 + u)⁻¹ = u / (1 + u) := by
          field_simp; ring
        linarith [heq ▸ hl]
      have hu2 : u / 2 ≤ u / (1 + u) :=
        div_le_div_of_nonneg_left hu0 (by linarith) (by linarith)
      have hloglb2 : u / 2 ≤ Real.log (1 + u) := le_trans hu2 hloglb
      have h1 : a * (u / 2) ≤ a * Real.log (1 + u) :=
        mul_le_mul_of_nonneg_left hloglb2 ha0
      have heqv : a * (u / 2) = a * u / 2 := by ring
      have hauval : a * u / 2 = Ctail ^ 2 * t / (4 * K * (1 + Se)) := by
        rw [hau]; field_simp; ring
      have hCtail_sq : 4 * (1 + Cexpect) * K ≤ Ctail ^ 2 := by
        have hnn : (0:ℝ) ≤ 4 * (1 + Cexpect) * K := by positivity
        calc 4 * (1 + Cexpect) * K
            = (Real.sqrt (4 * (1 + Cexpect) * K)) ^ 2 := (Real.sq_sqrt hnn).symm
          _ ≤ Ctail ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hCt2 2
      have hfrac : t ≤ Ctail ^ 2 * t / (4 * K * (1 + Se)) := by
        rw [le_div_iff₀ (by positivity : (0:ℝ) < 4 * K * (1 + Se))]
        have hstep : 4 * K * (1 + Se) ≤ Ctail ^ 2 := by
          calc 4 * K * (1 + Se) ≤ 4 * K * (1 + Cexpect) :=
                mul_le_mul_of_nonneg_left hSele (by positivity)
            _ = 4 * (1 + Cexpect) * K := by ring
            _ ≤ Ctail ^ 2 := hCtail_sq
        nlinarith [hstep, ht0]
      have hchain : t ≤ a * u / 2 := by rw [hauval]; exact hfrac
      linarith [h1, heqv, hchain]
  -- The witness for Ctail and c.
  refine ⟨max (2 * K / Real.log 2) (Real.sqrt (4 * (1 + Cexpect) * K)), 3, ?_, ?_, ?_⟩
  · -- 0 < Ctail
    have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    have : (0:ℝ) < 2 * K / Real.log 2 := by positivity
    exact lt_of_lt_of_le this (le_max_left _ _)
  · norm_num
  intro β μ₀ n r m hβ hμ₀ hn hr hm hdens
  -- Abbreviations
  set Ctail : ℝ := max (2 * K / Real.log 2) (Real.sqrt (4 * (1 + Cexpect) * K)) with hCtail
  -- Notation: L = log n
  set L : ℝ := Real.log (n : ℝ) with hL
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- positivity facts
  have hnR : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  have hrR : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have hμ₀0 : (0:ℝ) < μ₀ := lt_of_lt_of_le (by norm_num) hμ₀
  have hβ0 : (0:ℝ) < β := by linarith
  -- B
  set B : ℝ := 2 * μ₀ * (n:ℝ) * (r:ℝ) / (m:ℝ) with hB
  have hB0 : 0 < B := by
    rw [hB]; positivity
  -- Ctail positivity (reused)
  have hCtail0 : 0 < Ctail := by
    have : (0:ℝ) < 2 * K / Real.log 2 := by positivity
    rw [hCtail]; exact lt_of_lt_of_le this (le_max_left _ _)
  -- The scale function value
  -- s := sqrt of the argument
  set s : ℝ := Real.sqrt ((μ₀ * (n:ℝ) * (r:ℝ) * (β * L)) / (m:ℝ)) with hs
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  -- S C = C * s
  have hSeq : ∀ C : ℝ, tangentSamplingDeviationScale C β μ₀ n r m = C * s := by
    intro C
    rw [tangentSamplingDeviationScale, hs]
  -- Case split on whether n = 1 (i.e. L = 0) vs n ≥ 2 (L > 0).
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · -- n < 2 with 0 < n means n = 1: log 1 = 0, everything collapses to 3 ≤ 3.
    have hn1 : n = 1 := by omega
    have hnval : (n:ℝ) = 1 := by rw [hn1]; norm_num
    have hL0 : L = 0 := by rw [hL, hnval, Real.log_one]
    have hs00 : s = 0 := by
      rw [hs, hL0]
      simp
    -- S Ctail = 0, S Cexpect = 0
    have hSt : tangentSamplingDeviationScale Ctail β μ₀ n r m = 0 := by
      rw [hSeq, hs00, mul_zero]
    have hSe : tangentSamplingDeviationScale Cexpect β μ₀ n r m = 0 := by
      rw [hSeq, hs00, mul_zero]
    rw [hSt, hSe]
    -- LHS exp argument is 0
    have hzero : (-(0 / (K * B)) * Real.log (1 + B * 0 / (B + B * 0))) = 0 := by
      rw [zero_div, neg_zero, zero_mul]
    rw [hzero, Real.exp_zero, mul_one]
    -- RHS: 3 * (1:ℝ)^(-β) = 3
    rw [hnval]
    rw [show Real.rpow 1 (-β) = (1:ℝ) from Real.one_rpow _, mul_one]
  · -- main branch n ≥ 2, so L > 0
    have hnge : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn2
    have hL0 : 0 < L := by
      rw [hL]; apply Real.log_pos; linarith
    have hβL0 : 0 < β * L := mul_pos hβ0 hL0
    -- The argument of sqrt is ≥ 0 and ≤ 1.
    set arg : ℝ := (μ₀ * (n:ℝ) * (r:ℝ) * (β * L)) / (m:ℝ) with harg
    have harg0 : 0 ≤ arg := by rw [harg]; positivity
    -- density gives arg ≤ 1: μ₀ n r β L ≤ m
    have hdens' : μ₀ * (n:ℝ) * (r:ℝ) * (β * L) ≤ (m:ℝ) := by
      have : μ₀ * (r:ℝ) * β * (n:ℝ) * L = μ₀ * (n:ℝ) * (r:ℝ) * (β * L) := by ring
      rw [← this]; exact hdens
    have hargle1 : arg ≤ 1 := by
      rw [harg, div_le_one hmR]; exact hdens'
    -- s^2 = arg
    have hssq : s ^ 2 = arg := by
      rw [hs, Real.sq_sqrt harg0]
    have hsle1 : s ≤ 1 := by
      rw [hs]; rw [show (1:ℝ) = Real.sqrt 1 from (Real.sqrt_one).symm]
      exact Real.sqrt_le_sqrt hargle1
    -- The scales
    set St : ℝ := tangentSamplingDeviationScale Ctail β μ₀ n r m with hSt
    set Se : ℝ := tangentSamplingDeviationScale Cexpect β μ₀ n r m with hSe
    have hStv : St = Ctail * s := by rw [hSt, hSeq]
    have hSev : Se = Cexpect * s := by rw [hSe, hSeq]
    have hSt0 : 0 ≤ St := by rw [hStv]; positivity
    have hSe0 : 0 ≤ Se := by rw [hSev]; positivity
    -- u := (Ctail*s)/(1+Cexpect*s) and the inner-log argument equals 1+u
    -- First simplify the inner log argument.
    -- B*St/(B + B*Se) = St/(1+Se)  (cancel B>0)
    have h1Se : 0 < 1 + Se := by have := hSe0; linarith
    have hinner : B * St / (B + B * Se) = St / (1 + Se) := by
      rw [show B + B * Se = B * (1 + Se) by ring]
      rw [mul_div_mul_left _ _ (ne_of_gt hB0)]
    -- Now define E (the positive exponent)
    -- We will show E ≥ β*L where E = (St/(K*B)) * log(1 + St/(1+Se)).
    -- a := St/(K*B), u := St/(1+Se)
    set a : ℝ := St / (K * B) with ha
    set u : ℝ := St / (1 + Se) with hu
    have hKB0 : 0 < K * B := mul_pos hK hB0
    have ha0 : 0 ≤ a := by rw [ha]; positivity
    have hu0 : 0 ≤ u := by rw [hu]; positivity
    -- BOUND-A:  a ≥ (Ctail * β * L)/(2*K)
    -- s/B = sqrt(m β L /(4 μ₀ n r)) ≥ β L /2  from density.
    -- We prove  s / B ≥ β*L/2  directly.
    have hsB : s / B ≥ β * L / 2 := by
      -- s/B = s * m /(2 μ₀ n r); square it: s^2 m^2/(4μ₀²n²r²) = arg*m^2/(...)
      -- = (μ₀ n r β L/m)*m^2/(4μ₀²n²r²) = m β L/(4 μ₀ n r) ≥ (μ₀ r β n L) β L/(4μ₀ n r) = β²L²/4.
      -- So (s/B)^2 ≥ (βL/2)^2, both nonneg ⇒ s/B ≥ βL/2.
      have hsBnn : 0 ≤ s / B := by positivity
      have hbL2nn : 0 ≤ β * L / 2 := by positivity
      -- compute (s/B)^2
      have hsBsq : (s / B) ^ 2 = (m:ℝ) * (β * L) / (4 * μ₀ * (n:ℝ) * (r:ℝ)) := by
        rw [div_pow, hssq, harg, hB]
        field_simp
        ring
      have hposfac : 0 < (β * L) / (4 * μ₀ * (n:ℝ) * (r:ℝ)) := by positivity
      have hge : ((β * L / 2)) ^ 2 ≤ (s / B) ^ 2 := by
        rw [hsBsq]
        have hlhs : ((β * L / 2)) ^ 2
            = (μ₀ * (n:ℝ) * (r:ℝ) * (β * L)) * ((β * L) / (4 * μ₀ * (n:ℝ) * (r:ℝ))) := by
          field_simp; ring
        have hrhs : (m:ℝ) * (β * L) / (4 * μ₀ * (n:ℝ) * (r:ℝ))
            = (m:ℝ) * ((β * L) / (4 * μ₀ * (n:ℝ) * (r:ℝ))) := by
          ring
        rw [hlhs, hrhs]
        exact mul_le_mul_of_nonneg_right hdens' (le_of_lt hposfac)
      nlinarith [hge, hsBnn, hbL2nn]
    -- BOUND-A: a ≥ Ctail * (β*L) / (2*K)
    have hBoundA : a ≥ Ctail * (β * L) / (2 * K) := by
      -- a = St/(K*B) = (Ctail/K)*(s/B)
      have haeq : a = (Ctail / K) * (s / B) := by
        rw [ha, hStv]; field_simp
      rw [haeq]
      have hCtailK0 : 0 ≤ Ctail / K := by positivity
      have := mul_le_mul_of_nonneg_left hsB hCtailK0
      -- this : (Ctail/K)*(βL/2) ≤ (Ctail/K)*(s/B)
      have heq2 : Ctail / K * (β * L / 2) = Ctail * (β * L) / (2 * K) := by
        field_simp
      linarith [heq2 ▸ this]
    -- IDENTITY-1: a*u = Ctail^2 * (β*L) / (2*K*(1+Se))
    have hs2 : s ^ 2 = (β * L / 2) * B := by
      rw [hssq, harg, hB]; field_simp
    have hau : a * u = Ctail ^ 2 * (β * L) / (2 * K * (1 + Se)) := by
      have hBne : B ≠ 0 := ne_of_gt hB0
      have h1Se' : (1 + Se) ≠ 0 := ne_of_gt h1Se
      have hKne : K ≠ 0 := ne_of_gt hK
      rw [ha, hu, hStv, div_mul_div_comm]
      rw [show Ctail * s * (Ctail * s) = Ctail ^ 2 * s ^ 2 by ring, hs2]
      field_simp
    -- Extract Ctail bounds and the goal-arg rewrite BEFORE clearing the heavy let-values.
    have hCt1 : 2 * K / Real.log 2 ≤ Ctail := by rw [hCtail]; exact le_max_left _ _
    have hCt2 : Real.sqrt (4 * (1 + Cexpect) * K) ≤ Ctail := by
      rw [hCtail]; exact le_max_right _ _
    have hSele : 1 + Se ≤ 1 + Cexpect := by
      rw [hSev]
      have : Cexpect * s ≤ Cexpect := by
        calc Cexpect * s ≤ Cexpect * 1 := mul_le_mul_of_nonneg_left hsle1 (le_of_lt hCexpect)
          _ = Cexpect := mul_one _
      linarith
    -- Transform the goal's exp argument to -(a * log(1+u)) while the let-values are live.
    -- The main goal's first factor is already `a`; fold the inner log argument.
    rw [hinner]
    -- The goal is now  3 * exp (-a * log (1+u)) ≤ 3 * rpow n (-β).
    rw [show -a * Real.log (1 + u) = -(a * Real.log (1 + u)) from by ring]
    -- Now drop the heavy definitional let-bindings so linarith/nlinarith stay fast.
    clear_value a u St Se B s arg Ctail L
    -- 1 + u > 0
    have h1u : 0 < 1 + u := by linarith
    -- CRUX: E := a * log(1+u) ≥ β*L, via the isolated scalar lemma.
    have hE : β * L ≤ a * Real.log (1 + u) :=
      crux_E_ge K Cexpect Ctail Se a u (β * L)
        hK hCexpect hlog2 hβL0 ha0 hu0 h1Se h1u hSele hBoundA hau hCt1 hCt2
    -- 3 * exp(-(E)) ≤ 3 * exp(-(βL)) since E ≥ βL ⇒ -(E) ≤ -(βL)
    have hexp : Real.exp (-(a * Real.log (1 + u))) ≤ Real.exp (-(β * L)) :=
      Real.exp_le_exp.mpr (neg_le_neg hE)
    -- exp(-(βL)) = n^(-β)
    have hrpow : Real.exp (-(β * L)) = Real.rpow (n:ℝ) (-β) := by
      have hdef : Real.rpow (n:ℝ) (-β) = Real.exp (Real.log (n:ℝ) * (-β)) :=
        Real.rpow_def_of_pos hnR (-β)
      rw [hdef, hL]
      congr 1
      ring
    calc 3 * Real.exp (-(a * Real.log (1 + u)))
        ≤ 3 * Real.exp (-(β * L)) := by
          apply mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ = 3 * Real.rpow (n:ℝ) (-β) := by rw [hrpow]
