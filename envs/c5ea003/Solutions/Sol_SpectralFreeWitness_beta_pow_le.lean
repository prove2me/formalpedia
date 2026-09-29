-- Prove2me | solution 1 for SpectralFreeWitness.beta_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:40:03.182792+00:00
-- url     : https://prove2.me/submissions/88a2b524-2fab-45ec-bea1-9a053a1181b0

-- Sol generated from Speculative/AutoResearch/SpectralFreeWitness.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
/-
# The Spectral Free-Witness: Heat-Kernel Order Recovery

This file gives a complete, self-contained formal proof of the mechanism behind the
"heat-kernel free witness": the multiplicative order `r = ord_N(b)` is recovered
*exactly* from a **single** heat-kernel (return-probability) value of a half-lazy
random walk on the cyclic group `Z/rZ` with **lacunary dyadic** generators
`{±2^t : 0 ≤ t ≤ M}`, after `n = 8 (M+1)^2` diffusion steps, where `2^M ≥ N`.

The chain of results proved here:

* `cdist_double` — the *doubling step*: as long as the circle distance
  `d(x) = min (x % r) (r - x % r)` is below `r/4`, doubling `x` doubles `d`.
* `exists_dyadic_quarter` — the **doubling lemma**: for every `x ≢ 0 (mod r)`
  there is a dyadic shift `t ≤ M` (`r ≤ 2^M`) with `2^t x mod r ∈ [r/4, 3r/4]`.
* `cos_nonpos_of_cdist`, `dyadicEigen_le` — the resulting **spectral gap**:
  every nontrivial character eigenvalue satisfies `λ_k ≤ 1 - 1/(M+1)`, hence the
  half-lazy eigenvalue satisfies `0 ≤ μ_k ≤ 1 - 1/(2(M+1))`.
* `heatReturn_lower`, `heatReturn_upper` — the heat kernel at the identity
  satisfies `1/r ≤ p_n(e) ≤ 1/r + (1 - 1/(2(M+1)))^n`.
* `beta_pow_le` — the mixing estimate at the empirically observed step count
  `n = 8(M+1)^2`: the error is at most `1/(4N²)`.
* `round_one_div_of_close` — the rounding step.
* `heat_kernel_order_recovery` — **main theorem**: `round (1 / p_n(e)) = r`.
* `heat_kernel_recovers_orderOf` — the arithmetic corollary for the
  multiplicative order of a unit `b ∈ (Z/NZ)ˣ`.

Everything is unconditional; no `sorry`, no `native_decide`.
-/


open SpectralFreeWitness

open Finset Real

/-! ## 1. Circle distance and the doubling lemma -/







/-! ## 2. From the doubling lemma to a negative cosine -/


/-! ## 3. Spectral data of the lacunary dyadic walk -/











/-! ## 4. The heat kernel value at the identity -/



/-! ## 5. Mixing at `n = 8 (M+1)²` steps -/


/-! ## 6. Rounding recovers the order exactly -/


/-! ## 7. Main theorem: heat-kernel order recovery -/




open SpectralFreeWitness in
theorem solution(N M : ℕ) (hN : 0 < N) (hM : N ≤ 2 ^ M) :
    (1 - 1 / (2 * ((M : ℝ) + 1))) ^ (8 * (M + 1) ^ 2) ≤ 1 / (4 * (N : ℝ) ^ 2) := by
  have hMnn : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
  set D : ℝ := (M : ℝ) + 1 with hDdef
  have hD1 : (1 : ℝ) ≤ D := by rw [hDdef]; linarith
  have hD0 : (0 : ℝ) < D := by linarith
  have hδ1 : 1 / (2 * D) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have h0 : 0 ≤ 1 - 1 / (2 * D) := by linarith
  -- Step 1: `1 - δ ≤ exp (-δ)`
  have hexp1 : 1 - 1 / (2 * D) ≤ Real.exp (-(1 / (2 * D))) := by
    have := Real.add_one_le_exp (-(1 / (2 * D)))
    linarith
  have hpow : (1 - 1 / (2 * D)) ^ (8 * (M + 1) ^ 2)
      ≤ (Real.exp (-(1 / (2 * D)))) ^ (8 * (M + 1) ^ 2) :=
    pow_le_pow_left₀ h0 hexp1 _
  -- Step 2: identify the exponent
  have hcast : ((8 * (M + 1) ^ 2 : ℕ) : ℝ) = 8 * D ^ 2 := by
    rw [hDdef]; push_cast; ring
  have hexp2 : (Real.exp (-(1 / (2 * D)))) ^ (8 * (M + 1) ^ 2) = Real.exp (-(4 * D)) := by
    rw [← Real.exp_nat_mul, hcast]
    congr 1
    field_simp
    ring
  -- Step 3: `4 N² ≤ exp (4 D)`
  have hNle : (N : ℝ) ≤ 2 ^ M := by exact_mod_cast hM
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsq : (N : ℝ) ^ 2 ≤ ((2 : ℝ) ^ M) ^ 2 := by nlinarith [pow_pos (by norm_num : (0:ℝ) < 2) M]
  have e1 : ((2 : ℝ) ^ M) ^ 2 = 4 ^ M := by
    rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h4e : (4 : ℝ) ≤ Real.exp 4 := by
    have := Real.add_one_le_exp (4 : ℝ); linarith
  have e2 : (4 : ℝ) ^ M ≤ (Real.exp 4) ^ M := pow_le_pow_left₀ (by norm_num) h4e M
  have e3 : Real.exp (4 * D) = (Real.exp 4) ^ (M + 1) := by
    rw [← Real.exp_nat_mul]
    congr 1
    rw [hDdef]; push_cast; ring
  have hexpM : (0 : ℝ) < (Real.exp 4) ^ M := pow_pos (Real.exp_pos 4) M
  have h4N : 4 * (N : ℝ) ^ 2 ≤ Real.exp (4 * D) := by
    rw [e3, pow_succ]
    calc 4 * (N : ℝ) ^ 2 ≤ 4 * ((2 : ℝ) ^ M) ^ 2 := by linarith
      _ = 4 * (4 : ℝ) ^ M := by rw [e1]
      _ ≤ 4 * (Real.exp 4) ^ M := by linarith
      _ ≤ (Real.exp 4) ^ M * Real.exp 4 := by nlinarith
  -- Step 4: combine
  have hfin : Real.exp (-(4 * D)) ≤ 1 / (4 * (N : ℝ) ^ 2) := by
    rw [Real.exp_neg]
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by positivity) h4N
  calc (1 - 1 / (2 * D)) ^ (8 * (M + 1) ^ 2)
      ≤ (Real.exp (-(1 / (2 * D)))) ^ (8 * (M + 1) ^ 2) := hpow
    _ = Real.exp (-(4 * D)) := hexp2
    _ ≤ 1 / (4 * (N : ℝ) ^ 2) := hfin
