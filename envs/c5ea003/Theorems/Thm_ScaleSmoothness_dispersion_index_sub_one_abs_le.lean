-- Prove2me | Theorems.Thm_ScaleSmoothness_dispersion_index_sub_one_abs_le
-- name    : ScaleSmoothness.dispersion_index_sub_one_abs_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:52:00.245871+00:00
-- url     : https://prove2.me/theorems/a1098d08-881a-4a9c-a16d-e19961438b06
-- title:
--   Excess dispersion is bounded by the event rate.
-- statement:
--   **Excess dispersion is bounded by the event rate.**  With `S₂ = E[C²]`,
--   `|Var − λ·Mean-ratio| ≤ ...`: precisely, `|Var − Mean| ≤ Mean · (λ (S₂ − 1) + q S₂)`
--   whenever `Mean = λ ≥ 0`.
--
--   ```lean
--   theorem ScaleSmoothness.dispersion_index_sub_one_abs_le(w : Ω → ℚ) (P : Ω → K → ℚ) (val : K → ℚ)
--       (C : Ω → ℚ) (lam q : ℚ) (hlam : 0 ≤ lam)
--       (hP : ∀ ω, ∑ k, P ω k = 1) (hw : ∑ ω, w ω = 1) (hC : ∑ ω, w ω * C ω = 1)
--       (hmean : ∀ ω, condMean P val ω = lam * C ω)
--       (hvar : ∀ ω, condVar P val ω = lam * C ω * (1 - q * C ω))
--       (S₂ : ℚ) (hS₂ : ∑ ω, w ω * (C ω) ^ 2 = S₂) (hq : 0 ≤ q) (hS₂1 : 1 ≤ S₂) :
--       |mixVar w P val - mixMean w P val| ≤ lam * (lam * (S₂ - 1) + q * S₂) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/SmoothnessDispersionDecay.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/SmoothnessDispersionDecay.lean#L127

-- Thm stub generated from NumberTheory/SmoothnessDispersionDecay.lean
import Mathlib
import Definitions.Def_NumberTheory_SmoothnessDispersionDecay

/-!
# Why the per-`N` clustering dies at large `u`

The experiment of round-73 #4 (exp 562) left one phenomenon unexplained: the
per-`N` overdispersion of the smoothness rate is `D = 1.61 [1.50,1.73]` at the
bin `u ≈ 6` but `≈ 1.00` by the bins `u ≈ 7, 8`.  The exact results of
`Catalog.NumberTheory.ScaleSmoothnessDispersion` show that the *arithmetic* source
of the clustering — the structure correction `C(N)` — is completely
`u`-independent: its mean is exactly `1` and its variance is exactly
`dispersionBound a − 1` for every family of odd primes, with no reference to `u`
at all.  So the death of the clustering cannot be an arithmetic effect.

This file proves it is a *counting* effect.  In any mixture model in which the
number of smooth values found for a given `N` has conditional mean `λ·C(N)` and
conditional variance `λ·C(N)·(1 − q·C(N))` (the mean and variance of a count of
`n` independent trials of success probability `q·C(N)`, with `λ = n q`), the
dispersion index obeys the exact identity

  `Var = Mean · (1 + λ·(E[C²] − 1) − q·E[C²])`.

The arithmetic enters only through `E[C²] = dispersionBound a`, which is bounded
by `2`; the *observable* excess dispersion is proportional to the event rate `λ`.
At `u ≈ 6` the experiment had `λ` of order one and saw `D ≈ 1.6`; at `u ≈ 8` it
had `λ ≈ 18/4000 ≈ 0.005` and must see `D ≈ 1`, whatever the arithmetic.

## Main results

* `law_of_total_variance` — exact finite law of total variance for a mixture of
  finitely supported conditional distributions.
* `mixVar_eq` — the dispersion identity above.
* `dispersion_index_sub_one_abs_le` — `|Var/Mean − 1| ≤ λ (E[C²] − 1) + q E[C²]`.
* `smoothness_dispersion_identity` — the identity with `E[C²]` identified as the
  arithmetic quantity `dispersionBound a` for the structure correction of
  `x² − N`.
* `smoothness_dispersion_decays` — the payoff: for any family of distinct odd
  primes, `|Var − Mean| ≤ Mean · (λ + 2q)`.  The clustering is bounded by the
  event rate, uniformly in the smoothness bound, so it necessarily disappears
  where events become rare.
-/

open ScaleSmoothness

open Finset

/-! ### A finite law of total variance -/

variable {Ω : Type*} [Fintype Ω] {K : Type*} [Fintype K]






/-! ### The dispersion identity for a mixed count model -/

theorem ScaleSmoothness.dispersion_index_sub_one_abs_le(w : Ω → ℚ) (P : Ω → K → ℚ) (val : K → ℚ)
    (C : Ω → ℚ) (lam q : ℚ) (hlam : 0 ≤ lam)
    (hP : ∀ ω, ∑ k, P ω k = 1) (hw : ∑ ω, w ω = 1) (hC : ∑ ω, w ω * C ω = 1)
    (hmean : ∀ ω, condMean P val ω = lam * C ω)
    (hvar : ∀ ω, condVar P val ω = lam * C ω * (1 - q * C ω))
    (S₂ : ℚ) (hS₂ : ∑ ω, w ω * (C ω) ^ 2 = S₂) (hq : 0 ≤ q) (hS₂1 : 1 ≤ S₂) :
    |mixVar w P val - mixMean w P val| ≤ lam * (lam * (S₂ - 1) + q * S₂) := by sorry
