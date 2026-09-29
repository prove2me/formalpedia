-- Prove2me | solution 1 for mme_holder_subexp_capacity_omega_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T19:21:40.468199+00:00
-- url     : https://prove2.me/submissions/bed29851-cee3-4b04-833b-2c51f06db524

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Order.Filter.AtTopBot.Defs

open Real BigOperators Filter

universe u

/-- **The abstract Hölder + subexponential limit lemma.**

For real `ω ≥ 1`, `V > 1`, `R ≥ 1`, if there exists a polynomial-degree
`c : ℝ` and a sequence of "capacity witnesses" satisfying:

* the witness summand count `k_N` is polynomial in `N` (`k_N ≤ (N+1)^c`),
* every summand value `x_i` is nonnegative,
* the sum of values exceeds `V^N (1 - ε)`,
* the `ω`-power sum is bounded by `R^N`,

then `ω · log V ≤ log R`, equivalently `V^ω ≤ R`.

**Proof outline.** Apply Hölder's inequality with conjugate exponents
`(ω, ω/(ω-1))` to extract `(∑ x_i)^ω ≤ k_N^{ω-1} · ∑ x_i^ω`. Plug in
`∑ x_i ≥ V^N (1-ε)` and `∑ x_i^ω ≤ R^N`:

`V^{Nω}(1-ε)^ω ≤ k_N^{ω-1} · R^N ≤ ((N+1)^c)^{ω-1} · R^N`.

Take logs and rearrange:
`N · (ω log V − log R) ≤ c(ω−1) log(N+1) − ω log(1−ε)`.

If `ω log V > log R`, the LHS grows linearly while the RHS grows
logarithmically, giving a contradiction for large `N`. -/
theorem solution
    {ω V R : ℝ} (hω : 1 ≤ ω) (hV : 1 < V) (hR : 1 ≤ R)
    (hwitness : ∃ c : ℝ, ∀ ε > (0 : ℝ), ∃ᶠ N in atTop,
      ∃ (k : ℕ) (x : Fin k → ℝ),
        (k : ℝ) ≤ (N + 1 : ℝ) ^ c ∧
        (∀ i, 0 ≤ x i) ∧
        V ^ N * (1 - ε) ≤ ∑ i, x i ∧
        ∑ i, (x i) ^ ω ≤ R ^ N) :
    ω * Real.log V ≤ Real.log R := by
  -- Proof by contradiction: suppose `log R < ω log V`.
  by_contra hcontra
  have hcontra : Real.log R < ω * Real.log V := lt_of_not_ge hcontra
  -- Set up basic positivity facts.
  have hVpos : 0 < V := lt_trans zero_lt_one hV
  have hRpos : 0 < R := lt_of_lt_of_le zero_lt_one hR
  have hlogV_pos : 0 < Real.log V := Real.log_pos hV
  have hω_pos : 0 < ω := lt_of_lt_of_le zero_lt_one hω
  -- The gap γ := ω log V − log R is positive.
  set γ := ω * Real.log V - Real.log R with hγ_def
  have hγ_pos : 0 < γ := by
    simp [γ]; linarith
  -- Choose ε = 1/2; record log(1 − ε) = log(1/2).
  obtain ⟨c, hc⟩ := hwitness
  have hε_pos : (0 : ℝ) < (1/2 : ℝ) := by norm_num
  have hfreq := hc (1/2) hε_pos
  have h_one_minus_ε_pos : (0 : ℝ) < 1 - 1/2 := by norm_num
  -- log(1 − ε) is the constant `-log 2`, finite.
  set C₁ : ℝ := ω * Real.log (1 - (1/2 : ℝ)) with hC₁_def
  -- The RHS-budget function: ((ω-1)*c) * log(N+1) + (-C₁).
  -- Define `f N := (ω - 1) * c * Real.log (N + 1) - C₁`.
  -- We need: ∀ᶠ N in atTop, N * γ > f N — then witness gives contradiction.
  -- log (N+1) / N → 0, so any polynomial in log(N+1) is o(N).
  set α : ℝ := (ω - 1) * c with hα_def
  -- The key limit: `(α * Real.log (N + 1) - C₁) / N → 0`.
  -- Equivalently, `Real.log (N + 1) / N → 0` and constants over N → 0.
  -- Use `tendsto_pow_log_div_mul_add_atTop` with n=1, a=1, b=1: log x / (1*x+1) → 0.
  have hlog_div_lim : Tendsto (fun N : ℝ => Real.log (N + 1) / N) atTop (nhds 0) := by
    -- (log x)^1 / (1 * x + -1) → 0, then substitute x := N + 1 to get log(N+1)/N.
    have hbase : Tendsto (fun x : ℝ => Real.log x ^ 1 / (1 * x + (-1))) atTop (nhds 0) :=
      Real.tendsto_pow_log_div_mul_add_atTop 1 (-1) 1 one_ne_zero
    have hshift : Tendsto (fun N : ℝ => N + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 tendsto_id
    have hcomp := hbase.comp hshift
    refine hcomp.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with N _
    simp only [Function.comp, pow_one]
    congr 1
    ring
  -- Define `g N := α * Real.log (N + 1) - C₁`. Then `g N / N → 0`.
  have hg_div_lim : Tendsto (fun N : ℝ => (α * Real.log (N + 1) - C₁) / N) atTop (nhds 0) := by
    have h_const : Tendsto (fun N : ℝ => C₁ / N) atTop (nhds 0) := by
      exact tendsto_const_nhds.div_atTop tendsto_id
    have h_α : Tendsto (fun N : ℝ => α * (Real.log (N + 1) / N)) atTop (nhds 0) := by
      have := hlog_div_lim.const_mul α
      simpa using this
    have h_diff :
        Tendsto (fun N : ℝ => α * (Real.log (N + 1) / N) - C₁ / N) atTop (nhds 0) := by
      simpa using h_α.sub h_const
    refine h_diff.congr' ?_
    filter_upwards [eventually_ne_atTop (0:ℝ)] with N hN
    field_simp
  -- Choose N large enough that |g N / N| < γ ⇒ g N < N * γ.
  -- Use the limit + eventually_lt with bound γ > 0.
  have heventually : ∀ᶠ N : ℝ in atTop,
      (α * Real.log (N + 1) - C₁) < N * γ := by
    -- We want eventually `g N < N γ`.
    -- We have g N / N → 0, so eventually g N / N < γ.
    have h_lt : ∀ᶠ N : ℝ in atTop, (α * Real.log (N + 1) - C₁) / N < γ := by
      have := hg_div_lim.eventually_lt_const hγ_pos
      simpa using this
    filter_upwards [h_lt, eventually_gt_atTop (0:ℝ)] with N h_lt h_pos
    have h_eq : (α * Real.log (N + 1) - C₁) / N * N = α * Real.log (N + 1) - C₁ := by
      field_simp
    have : (α * Real.log (N + 1) - C₁) < γ * N := by
      have := (div_lt_iff₀ h_pos).mp h_lt
      linarith
    linarith
  -- Combine with the frequently statement to derive contradiction.
  -- Get a real N for which:
  --  (a) g N < N * γ
  --  (b) N > 0 (positivity for log, rpow manipulations)
  --  (c) the witness exists at N
  have hboth : ∃ᶠ N : ℝ in atTop, (∃ (k : ℕ) (x : Fin k → ℝ),
      (k : ℝ) ≤ (N + 1 : ℝ) ^ c ∧
      (∀ i, 0 ≤ x i) ∧
      V ^ N * (1 - 1/2 : ℝ) ≤ ∑ i, x i ∧
      ∑ i, (x i) ^ ω ≤ R ^ N) ∧
      ((α * Real.log (N + 1) - C₁) < N * γ) ∧ (0 < N) ∧ (1 < N) := by
    have h_ev : ∀ᶠ N : ℝ in atTop,
        ((α * Real.log (N + 1) - C₁) < N * γ) ∧ (0 < N) ∧ (1 < N) :=
      (heventually.and (eventually_gt_atTop (0:ℝ))).and (eventually_gt_atTop (1:ℝ))
        |>.mono fun N ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩
    exact hfreq.and_eventually h_ev
  rcases hboth.exists with ⟨N, ⟨⟨k, x, hk_bound, hx_nn, hxsum, hxpow⟩, hgN, hNpos, hNgt1⟩⟩
  -- Now derive the inequality (V^N * (1-1/2))^ω ≤ k^(ω-1) * R^N, etc.
  -- First handle k = 0 case (so sum = 0; this contradicts V^N * (1/2) ≤ 0).
  by_cases hk0 : k = 0
  · -- Empty index ⇒ sum is 0, so V^N * (1/2) ≤ 0, contradiction (V^N > 0).
    subst hk0
    have hsum0 : ∑ i : Fin 0, x i = 0 := by simp
    have hVNpos : 0 < V ^ N := Real.rpow_pos_of_pos hVpos N
    have hlhs_pos : 0 < V ^ N * (1 - 1/2 : ℝ) := by
      apply mul_pos hVNpos; norm_num
    rw [hsum0] at hxsum
    linarith
  · -- k ≥ 1. Hölder gives (∑ x_i)^ω ≤ k^(ω-1) · ∑ x_i^ω.
    have hk_ge1 : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hk0
    have hk_pos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
    -- Apply Hölder: rpow_sum_le_const_mul_sum_rpow_of_nonneg
    have hholder :
        (∑ i, x i) ^ ω ≤ ((Finset.univ : Finset (Fin k)).card : ℝ) ^ (ω - 1) *
          ∑ i, (x i) ^ ω :=
      Real.rpow_sum_le_const_mul_sum_rpow_of_nonneg (s := Finset.univ) (f := x) hω
        (fun i _ => hx_nn i)
    have h_card : ((Finset.univ : Finset (Fin k)).card : ℝ) = (k : ℝ) := by
      simp
    rw [h_card] at hholder
    -- Combine with the lower/upper bounds.
    -- Step 1: V^N * (1-1/2) ≤ ∑ x_i ⇒ (V^N * (1/2))^ω ≤ (∑ x_i)^ω since both nonneg.
    have hsum_nn : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx_nn i)
    have hVNpos : 0 < V ^ N := Real.rpow_pos_of_pos hVpos N
    have hlhs_pos : 0 < V ^ N * (1 - 1/2 : ℝ) := by
      apply mul_pos hVNpos; norm_num
    have hpow_lhs : (V ^ N * (1 - 1/2 : ℝ)) ^ ω ≤ (∑ i, x i) ^ ω := by
      apply Real.rpow_le_rpow (le_of_lt hlhs_pos) hxsum hω_pos.le
    -- Step 2: chain
    have hchain1 : (V ^ N * (1 - 1/2 : ℝ)) ^ ω ≤ (k : ℝ) ^ (ω - 1) * ∑ i, (x i) ^ ω :=
      le_trans hpow_lhs hholder
    have hkω1_nn : 0 ≤ (k : ℝ) ^ (ω - 1) := Real.rpow_nonneg hk_pos.le (ω - 1)
    have hxω_nn : 0 ≤ ∑ i, (x i) ^ ω :=
      Finset.sum_nonneg (fun i _ => Real.rpow_nonneg (hx_nn i) ω)
    have hRNpos : 0 < R ^ N := Real.rpow_pos_of_pos hRpos N
    have hchain2 : (k : ℝ) ^ (ω - 1) * ∑ i, (x i) ^ ω ≤ (k : ℝ) ^ (ω - 1) * R ^ N := by
      apply mul_le_mul_of_nonneg_left hxpow hkω1_nn
    -- Step 3: k^(ω-1) ≤ ((N+1)^c)^(ω-1). Need (N+1)^c > 0 (i.e. N+1 > 0).
    have hN1_pos : 0 < (N + 1 : ℝ) := by linarith
    have hNc_pos : 0 < (N + 1 : ℝ) ^ c := Real.rpow_pos_of_pos hN1_pos c
    have hω_minus1_nn : 0 ≤ ω - 1 := by linarith
    have hk_le_Nc : (k : ℝ) ≤ (N + 1 : ℝ) ^ c := hk_bound
    have hk_pow_le : (k : ℝ) ^ (ω - 1) ≤ ((N + 1 : ℝ) ^ c) ^ (ω - 1) := by
      apply Real.rpow_le_rpow hk_pos.le hk_le_Nc hω_minus1_nn
    have hchain3 : (k : ℝ) ^ (ω - 1) * R ^ N ≤ ((N + 1 : ℝ) ^ c) ^ (ω - 1) * R ^ N := by
      apply mul_le_mul_of_nonneg_right hk_pow_le hRNpos.le
    -- ((N+1)^c)^(ω-1) = (N+1)^(c*(ω-1)) = (N+1)^α (since α = (ω-1)*c).
    have h_rpow_mul : ((N + 1 : ℝ) ^ c) ^ (ω - 1) = (N + 1 : ℝ) ^ ((ω - 1) * c) := by
      rw [← Real.rpow_mul hN1_pos.le c (ω - 1), mul_comm c (ω - 1)]
    rw [h_rpow_mul] at hchain3
    -- α = (ω-1)*c definitionally.
    have hα_eq : α = (ω - 1) * c := hα_def
    -- So the chain becomes (V^N * (1/2))^ω ≤ (N+1)^α * R^N.
    have hfinal_ineq : (V ^ N * (1 - 1/2 : ℝ)) ^ ω ≤ (N + 1 : ℝ) ^ α * R ^ N := by
      calc (V ^ N * (1 - 1/2 : ℝ)) ^ ω
          ≤ (k : ℝ) ^ (ω - 1) * ∑ i, (x i) ^ ω := hchain1
        _ ≤ (k : ℝ) ^ (ω - 1) * R ^ N := hchain2
        _ ≤ (N + 1 : ℝ) ^ ((ω - 1) * c) * R ^ N := hchain3
        _ = (N + 1 : ℝ) ^ α * R ^ N := by rw [hα_eq]
    -- Now take logs. Both sides are positive.
    have hRHSpos : 0 < (N + 1 : ℝ) ^ α * R ^ N := mul_pos (Real.rpow_pos_of_pos hN1_pos α) hRNpos
    have hLHSpos : 0 < (V ^ N * (1 - 1/2 : ℝ)) ^ ω := Real.rpow_pos_of_pos hlhs_pos ω
    have hlog_ineq : Real.log ((V ^ N * (1 - 1/2 : ℝ)) ^ ω) ≤
        Real.log ((N + 1 : ℝ) ^ α * R ^ N) :=
      (Real.log_le_log_iff hLHSpos hRHSpos).mpr hfinal_ineq
    -- Expand both sides using log_rpow, log_mul.
    have hlog_lhs :
        Real.log ((V ^ N * (1 - 1/2 : ℝ)) ^ ω) =
          ω * (N * Real.log V + Real.log (1 - 1/2 : ℝ)) := by
      rw [Real.log_rpow hlhs_pos ω, Real.log_mul (ne_of_gt hVNpos) (by norm_num),
          Real.log_rpow hVpos N]
    have hlog_rhs :
        Real.log ((N + 1 : ℝ) ^ α * R ^ N) =
          α * Real.log (N + 1) + N * Real.log R := by
      rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hN1_pos α)) (ne_of_gt hRNpos),
          Real.log_rpow hN1_pos α, Real.log_rpow hRpos N]
    rw [hlog_lhs, hlog_rhs] at hlog_ineq
    -- Rearrange: ω * N * log V + ω * log(1/2) ≤ α * log(N+1) + N * log R.
    -- ⇒ N * (ω log V - log R) ≤ α log(N+1) - ω log(1/2) = α log(N+1) - C₁.
    have hC₁_eq : C₁ = ω * Real.log (1 - (1/2 : ℝ)) := hC₁_def
    have h_rearr : N * γ ≤ α * Real.log (N + 1) - C₁ := by
      have := hlog_ineq
      rw [hC₁_eq, hγ_def]
      nlinarith [hlog_ineq]
    -- This contradicts hgN : α * log(N+1) - C₁ < N * γ.
    linarith
