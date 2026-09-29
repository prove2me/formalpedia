-- Prove2me | Theorems.Thm_SpectralFreeWitness_heatReturn_approx_multiplicative
-- name    : SpectralFreeWitness.heatReturn_approx_multiplicative
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:51:10.994161+00:00
-- url     : https://prove2.me/theorems/2bfd870c-f544-4683-9e12-a11de8effdd9
-- title:
--   Critique of the "non-multiplicative" label.
-- statement:
--   **Critique of the "non-multiplicative" label.**  The heat-kernel witness value is
--   `1/r` up to `1/(4N²)`, hence as a function of the order it is multiplicative up to
--   `1/N²`.  What is non-multiplicative is the *mechanism* (a spectral aggregate over all
--   `r` eigenvalues), not the witness.
--
--   ```lean
--   theorem SpectralFreeWitness.heatReturn_approx_multiplicative(N M r₁ r₂ : ℕ) (h1 : 0 < r₁) (h2 : 0 < r₂)
--       (hr1 : r₁ ≤ N) (hr2 : r₂ ≤ N) (hprod : r₁ * r₂ ≤ N) (hM : N ≤ 2 ^ M) :
--       |heatReturn (r₁ * r₂) M (8 * (M + 1) ^ 2)
--         - heatReturn r₁ M (8 * (M + 1) ^ 2) * heatReturn r₂ M (8 * (M + 1) ^ 2)|
--         ≤ 1 / (N : ℝ) ^ 2 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/SpectralFreeWitnessSharp.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/SpectralFreeWitnessSharp.lean#L44

-- Thm stub generated from Speculative/AutoResearch/SpectralFreeWitnessSharp.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_SpectralFreeWitness
/-
# Sharpness, rigidity, and the arithmetic payload of the spectral free-witness

Adversarial follow-up to `Algebra.SpectralFreeWitness`:

* `heatReturn_injective` — **rigidity**: on the range `r ≤ N` the single heat-kernel
  value determines the order, so `r ↦ p_n(e)` is injective there.
* `heatReturn_approx_multiplicative` — an **honest correction** to the claim that the
  heat-kernel witness is "non-multiplicative": as a *function of the order* the witness
  value is multiplicative up to `1/N²`, since it is `1/r` to that accuracy.  Only the
  *mechanism* (a spectral aggregate) is non-multiplicative, not the witness value.
* `dyadicEigen_mersenne_ge`, `dyadic_gap_isTheta` — **sharpness**: for the Mersenne
  cycle length `r = 2^M - 1` the top nontrivial dyadic eigenvalue is at least
  `1 - 106/(M+1)`, so the spectral gap of the lacunary dyadic walk really is
  `Θ(1/M)`; the `O((log N)²)` mixing time cannot be improved to `O(log N)`
  by this generator set.
* `nontrivial_factor_of_sqrt_one`, `factor_from_even_order` — the **arithmetic
  payload**: a recovered even order with a non-trivial square root of `1` splits `N`.

No `sorry`, no `native_decide`.
-/


open SpectralFreeWitness

open Finset Real

/-! ## 1. Rigidity of the witness -/


/-! ## 2. The witness value is (approximately) multiplicative -/

theorem SpectralFreeWitness.heatReturn_approx_multiplicative(N M r₁ r₂ : ℕ) (h1 : 0 < r₁) (h2 : 0 < r₂)
    (hr1 : r₁ ≤ N) (hr2 : r₂ ≤ N) (hprod : r₁ * r₂ ≤ N) (hM : N ≤ 2 ^ M) :
    |heatReturn (r₁ * r₂) M (8 * (M + 1) ^ 2)
      - heatReturn r₁ M (8 * (M + 1) ^ 2) * heatReturn r₂ M (8 * (M + 1) ^ 2)|
      ≤ 1 / (N : ℝ) ^ 2 := by sorry
