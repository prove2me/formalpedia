-- Prove2me | solution 1 for SpectralFreeWitness.round_one_div_of_close
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:59:29.462073+00:00
-- url     : https://prove2.me/submissions/833a49ac-5f36-4cba-965d-d60bb0e761a3

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
theorem solution(r : ℕ) (p ε : ℝ) (hr : 0 < r) (hε : 0 ≤ ε)
    (h1 : 1 / (r : ℝ) ≤ p) (h2 : p ≤ 1 / (r : ℝ) + ε) (hb : 2 * (r : ℝ) ^ 2 * ε < 1) :
    round (1 / p) = (r : ℤ) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hp : 0 < p := lt_of_lt_of_le (by positivity) h1
  have hrp : 1 ≤ p * r := (div_le_iff₀ hr0).mp h1
  have hup : 1 / p ≤ (r : ℝ) := by
    rw [div_le_iff₀ hp]
    nlinarith
  have hlow : (r : ℝ) - 1 / 2 < 1 / p := by
    rw [lt_div_iff₀ hp]
    have hp2 : p * r ≤ 1 + (r : ℝ) * ε := by
      have hrw : ((1 : ℝ) / r + ε) * r = 1 + r * ε := by field_simp
      nlinarith
    nlinarith
  rw [round_eq, Int.floor_eq_iff]
  constructor
  · push_cast; linarith
  · push_cast; linarith
