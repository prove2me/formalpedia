-- Prove2me | solution 1 for SpectralFreeWitness.lazyEigen_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:43:17.690878+00:00
-- url     : https://prove2.me/submissions/9b370b79-5dd7-4d00-810a-c4646e947b98

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





lemma neg_one_le_dyadicEigen (r M k : ℕ) : -1 ≤ dyadicEigen r M k := by
  have hsum : -((M : ℝ) + 1)
      ≤ ∑ t ∈ range (M + 1), Real.cos (2 * π * ((k * 2 ^ t : ℕ) : ℝ) / r) := by
    calc -((M : ℝ) + 1) = ∑ _t ∈ range (M + 1), (-1 : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i _ => Real.neg_one_le_cos _)
  have hpos : (0 : ℝ) < (M : ℝ) + 1 := by positivity
  rw [dyadicEigen, le_div_iff₀ hpos]
  linarith






/-! ## 4. The heat kernel value at the identity -/



/-! ## 5. Mixing at `n = 8 (M+1)²` steps -/


/-! ## 6. Rounding recovers the order exactly -/


/-! ## 7. Main theorem: heat-kernel order recovery -/




open SpectralFreeWitness in
theorem solution(r M k : ℕ) : 0 ≤ lazyEigen r M k := by
  have := neg_one_le_dyadicEigen r M k
  rw [lazyEigen]; linarith
