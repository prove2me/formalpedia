-- Prove2me | solution 1 for SpectralFreeWitness.heat_kernel_order_recovery
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T08:10:06.838413+00:00
-- url     : https://prove2.me/submissions/2476c99e-963e-4915-a2f4-be5ee5b74a26

-- Sol generated from Speculative/AutoResearch/SpectralFreeWitness.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
import Theorems.Thm_SpectralFreeWitness_beta_pow_le
import Theorems.Thm_SpectralFreeWitness_heatReturn_lower
import Theorems.Thm_SpectralFreeWitness_heatReturn_upper
import Theorems.Thm_SpectralFreeWitness_round_one_div_of_close
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
theorem solution(N r M : ℕ) (hr : 0 < r) (hrN : r ≤ N) (hM : N ≤ 2 ^ M) :
    round (1 / heatReturn r M (8 * (M + 1) ^ 2)) = (r : ℤ) := by
  have hN : 0 < N := lt_of_lt_of_le hr hrN
  have hrM : r ≤ 2 ^ M := le_trans hrN hM
  have hlow := heatReturn_lower r M (8 * (M + 1) ^ 2) hr
  have hupp := heatReturn_upper r M (8 * (M + 1) ^ 2) hr hrM
  have hmix := beta_pow_le N M hN hM
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hrN' : (r : ℝ) ≤ N := by exact_mod_cast hrN
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  set ε : ℝ := 1 / (4 * (N : ℝ) ^ 2) with hε
  have hεpos : 0 < ε := by rw [hε]; positivity
  refine round_one_div_of_close r _ ε hr hεpos.le hlow (le_trans hupp (by linarith)) ?_
  have hrw : 2 * (r : ℝ) ^ 2 * ε = (r : ℝ) ^ 2 / (2 * (N : ℝ) ^ 2) := by
    rw [hε]; field_simp; ring
  rw [hrw, div_lt_one (by positivity)]
  nlinarith
