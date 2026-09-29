-- Prove2me | solution 1 for SpectralFreeWitness.heatReturn_lower
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T07:45:23.231163+00:00
-- url     : https://prove2.me/submissions/cd8d1618-9c43-4ba3-8d2a-b3e7d01206db

-- Sol generated from Speculative/AutoResearch/SpectralFreeWitness.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
import Theorems.Thm_SpectralFreeWitness_lazyEigen_nonneg
import Theorems.Thm_SpectralFreeWitness_lazyEigen_zero
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
theorem solution(r M n : ℕ) (hr : 0 < r) : 1 / (r : ℝ) ≤ heatReturn r M n := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hmem : 0 ∈ range r := mem_range.mpr hr
  have hsplit : ∑ k ∈ range r, (lazyEigen r M k) ^ n
      = (lazyEigen r M 0) ^ n + ∑ k ∈ (range r).erase 0, (lazyEigen r M k) ^ n :=
    (Finset.add_sum_erase _ _ hmem).symm
  have hrest : 0 ≤ ∑ k ∈ (range r).erase 0, (lazyEigen r M k) ^ n :=
    Finset.sum_nonneg (fun i _ => pow_nonneg (lazyEigen_nonneg _ _ _) _)
  rw [heatReturn, le_div_iff₀ hr0, hsplit, lazyEigen_zero r M]
  simp only [one_pow]
  have hcancel : 1 / (r : ℝ) * r = 1 := by field_simp
  rw [hcancel]
  linarith
