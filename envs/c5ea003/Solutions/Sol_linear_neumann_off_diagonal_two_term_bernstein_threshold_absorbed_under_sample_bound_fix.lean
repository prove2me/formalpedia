-- Prove2me | solution 1 for linear_neumann_off_diagonal_two_term_bernstein_threshold_absorbed_under_sample_bound_fix
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-06-25T02:09:24.576358+00:00
-- url     : https://prove2.me/submissions/825b815c-df59-48fa-84be-d8126ac180fd

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

open Real

set_option maxHeartbeats 2000000

theorem solution
    (Ctwo Centry Cfro : ℝ) :
    0 < Ctwo → 0 < Centry → 0 < Cfro →
    ∃ Ccoef : ℝ, 0 < Ccoef ∧
      ∀ (β lam : ℝ), 2 < β → 1 ≤ lam →
      ∀ (n₁ n₂ r m : ℕ) (μ₀ μ₁ : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        (m : ℝ) ≥
          lam * μ₁ * max μ₀ μ₁ *
            (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        Ctwo *
            (Real.sqrt
                (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
              (Cfro * μ₁ *
                Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                  Real.sqrt (μ₀ * (r : ℝ) / (↑(max n₁ n₂)))) +
              (((β + 2) * Real.log (↑(max n₁ n₂))) /
                  ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                (Centry * μ₁ *
                  Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                    (μ₀ * (r : ℝ) / (↑(max n₁ n₂))))) ≤
          Ccoef * μ₁ *
            Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
              Real.sqrt
                ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
                    (β * Real.log (↑(max n₁ n₂)))) / (m : ℝ)) := by
  intro hCtwo hCentry hCfro
  refine ⟨Ctwo * (Cfro * Real.sqrt 2 + 2 * Centry), ?_, ?_⟩
  · have : (0:ℝ) < Cfro * Real.sqrt 2 + 2 * Centry := by
      have h2 : (0:ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      positivity
    positivity
  intro β lam hβ hlam n₁ n₂ r m μ₀ μ₁ hn₁ hn₂ hr hmN hμ₀ hμ₁ hsample
  classical
  -- abbreviations
  set n : ℝ := (↑(max n₁ n₂) : ℝ) with hn
  set L : ℝ := Real.log (↑(max n₁ n₂)) with hL
  set N : ℝ := (n₁ : ℝ) * (n₂ : ℝ) with hNdef
  set base : ℝ := Real.sqrt ((r : ℝ) / N) with hbase
  -- positivity / nonnegativity facts
  have hn1R : (0:ℝ) < (n₁ : ℝ) := by exact_mod_cast hn₁
  have hn2R : (0:ℝ) < (n₂ : ℝ) := by exact_mod_cast hn₂
  have hrR : (0:ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hNpos : (0:ℝ) < N := by rw [hNdef]; positivity
  have hmax_pos : 0 < max n₁ n₂ := lt_of_lt_of_le hn₁ (le_max_left _ _)
  have hnpos : (0:ℝ) < n := by rw [hn]; exact_mod_cast hmax_pos
  have hn_ge1 : (1:ℝ) ≤ n := by rw [hn]; exact_mod_cast hmax_pos
  have hLnonneg : 0 ≤ L := by rw [hL]; exact Real.log_nonneg hn_ge1
  have hβpos : (0:ℝ) < β := by linarith
  have hμ₀pos : (0:ℝ) < μ₀ := by linarith
  have hμ₁pos : (0:ℝ) < μ₁ := by linarith
  have hbeta2pos : (0:ℝ) < β + 2 := by linarith
  have hbasenn : 0 ≤ base := Real.sqrt_nonneg _
  -- N ≤ n^2  (since n = max n₁ n₂ ≥ each)
  have hNle : N ≤ n ^ 2 := by
    rw [hNdef, hn]
    have h1 : (n₁ : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by exact_mod_cast le_max_left n₁ n₂
    have h2 : (n₂ : ℝ) ≤ (↑(max n₁ n₂) : ℝ) := by exact_mod_cast le_max_right n₁ n₂
    have h1n : (0:ℝ) ≤ (n₁:ℝ) := le_of_lt hn1R
    have h2n : (0:ℝ) ≤ (n₂:ℝ) := le_of_lt hn2R
    calc (n₁ : ℝ) * (n₂ : ℝ) ≤ (↑(max n₁ n₂) : ℝ) * (↑(max n₁ n₂) : ℝ) :=
          mul_le_mul h1 h2 h2n (le_trans h1n h1)
      _ = (↑(max n₁ n₂) : ℝ) ^ 2 := by ring
  -- the RHS is always ≥ 0
  have hRHSnn : 0 ≤ Ctwo * (Cfro * Real.sqrt 2 + 2 * Centry) * μ₁ * base *
      Real.sqrt ((μ₀ * n * (r : ℝ) * (β * L)) / (m : ℝ)) := by
    have h2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have : (0:ℝ) ≤ Cfro * Real.sqrt 2 + 2 * Centry := by positivity
    positivity
  -- CASE 1: L = 0  ⟹  LHS = 0 ≤ RHS
  rcases eq_or_lt_of_le hLnonneg with hL0 | hLpos
  · -- L = 0
    have hKzero : (β + 2) * L = 0 := by rw [← hL0]; ring
    -- LHS factors all contain ((β+2)*L) either directly or under sqrt; both vanish
    rw [hn, hL, hNdef] at *
    -- rewrite the goal's (β+2)*log = 0
    simp only [← hL] at *
    rw [show (β + 2) * L = 0 from hKzero]
    simp only [zero_div, Real.sqrt_zero, zero_mul, mul_zero, add_zero]
    -- goal: 0 ≤ RHS
    have h2 : (0:ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    have hpc : (0:ℝ) ≤ Cfro * Real.sqrt 2 + 2 * Centry := by positivity
    positivity
  -- CASE 2: 0 < L
  · -- sample lower bound gives m > 0
    have hmaxpos : 0 < max μ₀ μ₁ := lt_of_lt_of_le hμ₀pos (le_max_left _ _)
    have hlampos : (0:ℝ) < lam := by linarith
    have hsample' : lam * μ₁ * max μ₀ μ₁ * n * (r : ℝ) * (β * L) ≤ (m : ℝ) := by
      rw [hn, hL]; exact hsample
    have hrhs_pos : (0:ℝ) < lam * μ₁ * max μ₀ μ₁ * n * (r : ℝ) * (β * L) := by
      positivity
    have hmpos : (0:ℝ) < (m : ℝ) := lt_of_lt_of_le hrhs_pos hsample'
    -- m ≥ μ₀ * n * r * (β * L)  (drop lam ≥ 1, μ₁ ≥ 1, max μ₀ μ₁ ≥ μ₀)
    have hm_lower : μ₀ * n * (r : ℝ) * (β * L) ≤ (m : ℝ) := by
      have hstep : μ₀ * n * (r : ℝ) * (β * L)
          ≤ lam * μ₁ * max μ₀ μ₁ * n * (r : ℝ) * (β * L) := by
        have h1 : μ₀ ≤ lam * μ₁ * max μ₀ μ₁ := by
          have hmaxμ : μ₀ ≤ max μ₀ μ₁ := le_max_left _ _
          calc μ₀ = 1 * 1 * μ₀ := by ring
            _ ≤ lam * μ₁ * max μ₀ μ₁ :=
                  mul_le_mul (mul_le_mul hlam hμ₁ (by norm_num) (le_of_lt hlampos))
                    hmaxμ (le_of_lt hμ₀pos)
                    (by positivity)
        have hnn : 0 ≤ n * (r : ℝ) * (β * L) := by positivity
        nlinarith [hnn, h1, hμ₀pos]
      linarith
    -- Notation: K = (β+2)*L, p = m/N, Y = √(μ₀*n*r*(β*L)/m)
    set K : ℝ := (β + 2) * L with hKdef
    set p : ℝ := (m : ℝ) / N with hpdef
    set Y : ℝ := Real.sqrt ((μ₀ * n * (r : ℝ) * (β * L)) / (m : ℝ)) with hYdef
    have hKpos : 0 < K := by rw [hKdef]; positivity
    have hppos : 0 < p := by rw [hpdef]; positivity
    have hYsq : Y ^ 2 = (μ₀ * n * (r : ℝ) * (β * L)) / (m : ℝ) := by
      rw [hYdef]; exact Real.sq_sqrt (by positivity)
    have hYnn : 0 ≤ Y := Real.sqrt_nonneg _
    -- INNER 1:  √(K/p) * √(μ₀*r/n) ≤ √2 * Y
    have hInner1 : Real.sqrt (K / p) * Real.sqrt (μ₀ * (r:ℝ) / n) ≤ Real.sqrt 2 * Y := by
      have hlhs_eq : Real.sqrt (K / p) * Real.sqrt (μ₀ * (r:ℝ) / n)
          = Real.sqrt ((K / p) * (μ₀ * (r:ℝ) / n)) := by
        rw [← Real.sqrt_mul (by positivity)]
      have hrhs_eq : Real.sqrt 2 * Y = Real.sqrt (2 * ((μ₀ * n * (r : ℝ) * (β * L)) / (m : ℝ))) := by
        rw [hYdef, ← Real.sqrt_mul (by norm_num)]
      rw [hlhs_eq, hrhs_eq]
      apply Real.sqrt_le_sqrt
      -- reduce to: (K/p)*(μ₀ r/n) ≤ 2 * (μ₀ n r (βL)/m)
      have hKp : K / p = (β + 2) * L * N / (m : ℝ) := by
        rw [hKdef, hpdef]; field_simp
      rw [hKp]
      -- LHS = ((β+2)L N * μ₀ r)/(m*n);  RHS = 2*(μ₀ n r (βL))/m = (2 μ₀ n r (βL))/m
      rw [div_mul_div_comm]
      rw [show 2 * ((μ₀ * n * (r : ℝ) * (β * L)) / (m : ℝ))
            = (2 * (μ₀ * n * (r:ℝ) * (β * L))) / (m : ℝ) by ring]
      rw [div_le_div_iff₀ (by positivity) hmpos]
      -- goal: ((β+2)*L*N * (μ₀*r)) * m ≤ (2*(μ₀*n*r*(β*L))) * (m*n)
      have hkey : (β + 2) * N ≤ 2 * β * n ^ 2 := by nlinarith [hNle, hβpos, hnpos, sq_nonneg n]
      have hcoef : (0:ℝ) ≤ μ₀ * (r:ℝ) * L * (m:ℝ) := by positivity
      have hmul := mul_le_mul_of_nonneg_right hkey hcoef
      -- hmul : ((β+2)*N) * (μ₀ r L m) ≤ (2 β n^2) * (μ₀ r L m)
      ring_nf
      ring_nf at hmul
      linarith [hmul]
    -- INNER 2:  (K/p) * (μ₀*r/n) ≤ 2 * Y
    have hInner2 : (K / p) * (μ₀ * (r:ℝ) / n) ≤ 2 * Y := by
      -- Square-free route: since both sides ≥ 0, show LHS ≤ 2*Y via LHS^2 ≤ (2Y)^2 = 4 Y^2
      have hLHSnn : 0 ≤ (K / p) * (μ₀ * (r:ℝ) / n) := by positivity
      have h2Ynn : 0 ≤ 2 * Y := by positivity
      rw [← Real.sqrt_sq hLHSnn]
      have hgoal : ((K / p) * (μ₀ * (r:ℝ) / n)) ^ 2 ≤ (2 * Y) ^ 2 := by
        have hKp : K / p = (β + 2) * L * N / (m : ℝ) := by
          rw [hKdef, hpdef]; field_simp
        have h2Ysq : (2 * Y) ^ 2 = (4 * (μ₀ * n * (r : ℝ) * (β * L))) / (m : ℝ) := by
          rw [mul_pow]; rw [hYsq]; ring
        have hLHSval : ((K / p) * (μ₀ * (r:ℝ) / n)) ^ 2
            = (((β + 2) * L * N) ^ 2 * (μ₀ * (r:ℝ)) ^ 2) / ((m:ℝ) ^ 2 * n ^ 2) := by
          rw [hKp]; rw [div_mul_div_comm, div_pow]; ring_nf
        rw [hLHSval, h2Ysq, div_le_div_iff₀ (by positivity) hmpos]
        -- goal: ((β+2)*L*N)^2 * (μ₀*r)^2 * m ≤ (4*(μ₀*n*r*(β*L))) * (m^2*n^2)
        have hkey : (β + 2) * N ≤ 2 * β * n ^ 2 := by nlinarith [hNle, hβpos, hnpos, sq_nonneg n]
        -- nonneg base quantities
        have hNnn : 0 ≤ N := le_of_lt hNpos
        have hkeynn : 0 ≤ (β + 2) * N := by positivity
        have hkey2nn : 0 ≤ 2 * β * n ^ 2 := by positivity
        -- Step A: ((β+2)*N)^2 ≤ (2*β*n^2)^2
        have hsqkey : ((β + 2) * N) ^ 2 ≤ (2 * β * n ^ 2) ^ 2 :=
          pow_le_pow_left₀ hkeynn hkey 2
        -- common nonneg multiplier  M1 := L^2 * (μ₀*r)^2 * m
        have hM1 : 0 ≤ L ^ 2 * (μ₀ * (r:ℝ)) ^ 2 * (m:ℝ) := by positivity
        -- LHS ≤ (2βn^2)^2 * L^2 (μ₀r)^2 m
        have hUpper : ((β + 2) * L * N) ^ 2 * (μ₀ * (r:ℝ)) ^ 2 * (m:ℝ)
            ≤ (2 * β * n ^ 2) ^ 2 * (L ^ 2 * (μ₀ * (r:ℝ)) ^ 2 * (m:ℝ)) := by
          have hre : ((β + 2) * L * N) ^ 2 * (μ₀ * (r:ℝ)) ^ 2 * (m:ℝ)
              = ((β + 2) * N) ^ 2 * (L ^ 2 * (μ₀ * (r:ℝ)) ^ 2 * (m:ℝ)) := by ring
          rw [hre]; exact mul_le_mul_of_nonneg_right hsqkey hM1
        -- Step B: (2βn^2)^2 L^2 (μ₀r)^2 m ≤ 4 μ₀ n r βL * (m n^2) (= RHS)
        -- use m ≥ μ₀ n r (βL): 4 μ₀ n r βL * m * n^2 ≥ 4 μ₀ n r βL * (μ₀ n r βL) * n^2
        --   = 4 (μ₀ n r βL)^2 n^2 = 4 β^2 L^2 μ₀^2 r^2 n^4 = (2βn^2)^2 L^2 (μ₀ r)^2
        -- but we need the extra m factor on the LHS-upper. So multiply absorption by m:
        have hLower : (2 * β * n ^ 2) ^ 2 * (L ^ 2 * (μ₀ * (r:ℝ)) ^ 2 * (m:ℝ))
            ≤ (4 * (μ₀ * n * (r:ℝ) * (β * L))) * ((m:ℝ) ^ 2 * n ^ 2) := by
          -- (2βn^2)^2 L^2 (μ₀r)^2 m = 4 (μ₀nrβL)^2 n^2 m ;  RHS = 4 μ₀nrβL m^2 n^2.
          -- Suffices  4 (μ₀nrβL)^2 n^2 m ≤ 4 μ₀nrβL m^2 n^2, i.e. (μ₀nrβL) m ≤ m^2  (×4 n^2 μ₀nrβL≥0)
          have hmabs : (μ₀ * n * (r:ℝ) * (β * L)) * (m:ℝ) ≤ (m:ℝ) * (m:ℝ) :=
            mul_le_mul_of_nonneg_right hm_lower (le_of_lt hmpos)
          have hcoef : 0 ≤ 4 * n ^ 2 * (μ₀ * n * (r:ℝ) * (β * L)) := by positivity
          have hstep := mul_le_mul_of_nonneg_left hmabs hcoef
          nlinarith [hstep]
        calc ((β + 2) * L * N) ^ 2 * (μ₀ * (r:ℝ)) ^ 2 * (m:ℝ)
            ≤ (2 * β * n ^ 2) ^ 2 * (L ^ 2 * (μ₀ * (r:ℝ)) ^ 2 * (m:ℝ)) := hUpper
          _ ≤ (4 * (μ₀ * n * (r:ℝ) * (β * L))) * ((m:ℝ) ^ 2 * n ^ 2) := hLower
      calc Real.sqrt (((K / p) * (μ₀ * (r:ℝ) / n)) ^ 2)
          ≤ Real.sqrt ((2 * Y) ^ 2) := Real.sqrt_le_sqrt hgoal
        _ = 2 * Y := Real.sqrt_sq h2Ynn
    -- Assemble: LHS = Ctwo*(T1+T2) ≤ Ctwo*(Cfro√2+2Centry)*μ₁*base*Y = RHS
    have hμ₁nn : 0 ≤ μ₁ := le_of_lt hμ₁pos
    have hCμb : 0 ≤ μ₁ * base := by positivity
    -- T1term ≤ Cfro*μ₁*base*(√2*Y)
    have hT1 : Real.sqrt (K / p) * (Cfro * μ₁ * base * Real.sqrt (μ₀ * (r:ℝ) / n))
        ≤ Cfro * μ₁ * base * (Real.sqrt 2 * Y) := by
      have hfac : Real.sqrt (K / p) * (Cfro * μ₁ * base * Real.sqrt (μ₀ * (r:ℝ) / n))
          = (Cfro * μ₁ * base) * (Real.sqrt (K / p) * Real.sqrt (μ₀ * (r:ℝ) / n)) := by ring
      rw [hfac]
      exact mul_le_mul_of_nonneg_left hInner1 (by positivity)
    -- T2term ≤ Centry*μ₁*base*(2*Y)
    have hT2 : (K / p) * (Centry * μ₁ * base * (μ₀ * (r:ℝ) / n))
        ≤ Centry * μ₁ * base * (2 * Y) := by
      have hfac : (K / p) * (Centry * μ₁ * base * (μ₀ * (r:ℝ) / n))
          = (Centry * μ₁ * base) * ((K / p) * (μ₀ * (r:ℝ) / n)) := by ring
      rw [hfac]
      exact mul_le_mul_of_nonneg_left hInner2 (by positivity)
    calc Ctwo * (Real.sqrt (K / p) * (Cfro * μ₁ * base * Real.sqrt (μ₀ * (r:ℝ) / n))
              + (K / p) * (Centry * μ₁ * base * (μ₀ * (r:ℝ) / n)))
        ≤ Ctwo * (Cfro * μ₁ * base * (Real.sqrt 2 * Y) + Centry * μ₁ * base * (2 * Y)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hCtwo)
          exact add_le_add hT1 hT2
      _ = Ctwo * (Cfro * Real.sqrt 2 + 2 * Centry) * μ₁ * base * Y := by ring

