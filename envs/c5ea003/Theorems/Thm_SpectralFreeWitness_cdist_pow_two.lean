-- Prove2me | Theorems.Thm_SpectralFreeWitness_cdist_pow_two
-- name    : SpectralFreeWitness.cdist_pow_two
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:50:16.528322+00:00
-- url     : https://prove2.me/theorems/8a525372-ec43-4835-867f-aa59bf23d552
-- title:
--   Iterated doubling, as long as we stay below the quarter threshold.
-- statement:
--   Iterated doubling, as long as we stay below the quarter threshold.
--
--   ```lean
--   theorem SpectralFreeWitness.cdist_pow_two(r x M : ℕ) (hr : 0 < r) (hx : x % r ≠ 0)
--       (hstay : ∀ t ≤ M, 4 * cdist r (2 ^ t * x) < r) :
--       ∀ t ≤ M, cdist r (2 ^ t * x) = 2 ^ t * cdist r x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/SpectralFreeWitness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/SpectralFreeWitness.lean#L67

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

theorem SpectralFreeWitness.cdist_pow_two(r x M : ℕ) (hr : 0 < r) (hx : x % r ≠ 0)
    (hstay : ∀ t ≤ M, 4 * cdist r (2 ^ t * x) < r) :
    ∀ t ≤ M, cdist r (2 ^ t * x) = 2 ^ t * cdist r x := by sorry
