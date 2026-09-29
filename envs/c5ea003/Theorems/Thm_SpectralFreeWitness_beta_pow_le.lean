-- Prove2me | Theorems.Thm_SpectralFreeWitness_beta_pow_le
-- name    : SpectralFreeWitness.beta_pow_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:50:34.603661+00:00
-- url     : https://prove2.me/theorems/6282feff-6ab8-41ae-b151-c952d69a10d1
-- title:
--   The quantitative mixing estimate: after `n = 8 (M+1)²` half-lazy steps the
-- statement:
--   The quantitative mixing estimate: after `n = 8 (M+1)²` half-lazy steps the
--   spectral error is below `1/(4N²)`, for any `N ≤ 2^M`.
--
--   ```lean
--   theorem SpectralFreeWitness.beta_pow_le(N M : ℕ) (hN : 0 < N) (hM : N ≤ 2 ^ M) :
--       (1 - 1 / (2 * ((M : ℝ) + 1))) ^ (8 * (M + 1) ^ 2) ≤ 1 / (4 * (N : ℝ) ^ 2) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/SpectralFreeWitness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/SpectralFreeWitness.lean#L283

-- Thm stub generated from Speculative/AutoResearch/SpectralFreeWitness.lean
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

theorem SpectralFreeWitness.beta_pow_le(N M : ℕ) (hN : 0 < N) (hM : N ≤ 2 ^ M) :
    (1 - 1 / (2 * ((M : ℝ) + 1))) ^ (8 * (M + 1) ^ 2) ≤ 1 / (4 * (N : ℝ) ^ 2) := by sorry
