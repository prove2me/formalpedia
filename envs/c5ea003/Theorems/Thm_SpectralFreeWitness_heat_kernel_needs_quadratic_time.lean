-- Prove2me | Theorems.Thm_SpectralFreeWitness_heat_kernel_needs_quadratic_time
-- name    : SpectralFreeWitness.heat_kernel_needs_quadratic_time
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:51:51.647501+00:00
-- url     : https://prove2.me/theorems/5276b8f2-fd34-4772-b946-1fc96fda8cdd
-- title:
--   Necessity of quadratic diffusion time.
-- statement:
--   **Necessity of quadratic diffusion time.**  For the Mersenne cycle
--   `r = 2^M - 1` with `M ≥ 106`, any step count with `154 n ≤ M (M+1)` makes the rounding
--   of the heat-kernel value miss the order.
--
--   ```lean
--   theorem SpectralFreeWitness.heat_kernel_needs_quadratic_time(M n : ℕ) (hM : 106 ≤ M)
--       (hn : 154 * n ≤ M * (M + 1)) :
--       round (1 / heatReturn (2 ^ M - 1) M n) ≠ ((2 ^ M - 1 : ℕ) : ℤ) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/SpectralFreeWitnessLower.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/SpectralFreeWitnessLower.lean#L78

-- Thm stub generated from Speculative/AutoResearch/SpectralFreeWitnessLower.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
/-
# A matching lower bound: the diffusion really needs `Θ((log N)²)` steps

`Algebra.SpectralFreeWitness` proves that `n = 8 (M+1)²` half-lazy diffusion steps
suffice for exact order recovery.  Here we prove the converse for the extremal
Mersenne cycle `r = 2^M - 1`: if `154 n ≤ M (M+1)` then the rounding **fails**,

  `round (1 / p_n(e)) ≠ r`,

so the quadratic step count is not an artefact of the analysis — the lacunary dyadic
diffusion genuinely needs `Ω((log N)²)` steps.  Together with the upper bound this
pins the diffusion time of the spectral free-witness at `Θ((log N)²)`.

Ingredients:

* `exp_neg_two_mul_le_one_sub` — the elementary bound `e^{-2δ} ≤ 1 - δ` for `δ ≤ 1/2`
  (the reverse of the usual `1 - δ ≤ e^{-δ}`), which converts the sharpness bound on
  the top eigenvalue into a lower bound on its `n`-th power.
* `lazyEigen_mersenne_ge` — `μ₁ ≥ 1 - 53/(M+1)` from the sharpness result.
* `heatReturn_ge_two_terms` — dropping all but the two leading spectral terms.

No `sorry`, no `native_decide`.
-/


open SpectralFreeWitness

open Finset Real

theorem SpectralFreeWitness.heat_kernel_needs_quadratic_time(M n : ℕ) (hM : 106 ≤ M)
    (hn : 154 * n ≤ M * (M + 1)) :
    round (1 / heatReturn (2 ^ M - 1) M n) ≠ ((2 ^ M - 1 : ℕ) : ℤ) := by sorry
