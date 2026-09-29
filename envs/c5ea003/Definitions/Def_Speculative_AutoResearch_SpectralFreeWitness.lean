-- Prove2me | Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
-- name    : Speculative_AutoResearch_SpectralFreeWitness
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:30:18.973586+00:00
-- url     : https://prove2.me/theorems/4dde3db0-eef2-4d52-a3e5-f7096d33f84b
-- title:
--   Aether Catalog definitions — Speculative_AutoResearch_SpectralFreeWitness
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.AutoResearch.SpectralFreeWitness`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/AutoResearch/SpectralFreeWitness.lean by skeleton subtraction
import Mathlib
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


namespace SpectralFreeWitness

open Finset Real

/-! ## 1. Circle distance and the doubling lemma -/

/-- The circle distance of `x` from `0` in `Z/rZ`, i.e. `min (x mod r) (r - x mod r)`. -/
def cdist (r x : ℕ) : ℕ := min (x % r) (r - x % r)






/-! ## 2. From the doubling lemma to a negative cosine -/


/-! ## 3. Spectral data of the lacunary dyadic walk -/

/-- The character eigenvalue of the (non-lazy) lacunary dyadic walk on `Z/rZ`:
`λ_k = (1/(M+1)) ∑_{t=0}^{M} cos(2π k 2^t / r)`. -/
noncomputable def dyadicEigen (r M k : ℕ) : ℝ :=
  (∑ t ∈ range (M + 1), Real.cos (2 * π * ((k * 2 ^ t : ℕ) : ℝ) / r)) / (M + 1)

/-- The eigenvalue of the half-lazy walk `W = (I + P)/2`. -/
noncomputable def lazyEigen (r M k : ℕ) : ℝ := (1 + dyadicEigen r M k) / 2

/-- The heat kernel of the half-lazy walk at the identity after `n` steps,
`p_n(e) = (1/r) ∑_k μ_k^n`. -/
noncomputable def heatReturn (r M n : ℕ) : ℝ :=
  (∑ k ∈ range r, (lazyEigen r M k) ^ n) / r








/-! ## 4. The heat kernel value at the identity -/



/-! ## 5. Mixing at `n = 8 (M+1)²` steps -/


/-! ## 6. Rounding recovers the order exactly -/


/-! ## 7. Main theorem: heat-kernel order recovery -/



end SpectralFreeWitness


