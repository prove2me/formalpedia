-- Prove2me | Theorems.Thm_ScaleSmoothness_smoothness_dispersion_decays
-- name    : ScaleSmoothness.smoothness_dispersion_decays
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T22:52:44.221333+00:00
-- url     : https://prove2.me/theorems/eed2b1f6-34ed-498e-8faa-c369beb55ee2
-- title:
--   The clustering dies with the event rate.
-- statement:
--   **The clustering dies with the event rate.**  For any family of *distinct* odd
--   primes, the excess of the variance over the mean is at most `Mean·(λ + 2q)`.
--   Since the arithmetic factor `dispersionBound a` is capped at `2` uniformly in the
--   smoothness bound, an observed overdispersion can only be of size `O(λ)`: where
--   smooth events are rare (large `u`), the per-`N` clustering must vanish, even
--   though the underlying arithmetic bias is unchanged.
--
--   ```lean
--   theorem ScaleSmoothness.smoothness_dispersion_decays(a : ι → ℕ) [∀ i, Fact (a i).Prime]
--       (hodd : ∀ i, a i ≠ 2) (hinj : Function.Injective a) {K : Type*} [Fintype K]
--       (P : (∀ i, ZMod (a i)) → K → ℚ) (val : K → ℚ) (lam q : ℚ)
--       (hlam : 0 ≤ lam) (hq : 0 ≤ q)
--       (hP : ∀ N, ∑ k, P N k = 1)
--       (hmean : ∀ N, condMean P val N = lam * structureCorrection a N)
--       (hvar : ∀ N, condVar P val N = lam * structureCorrection a N
--         * (1 - q * structureCorrection a N)) :
--       |mixVar (uniformWeight a) P val - mixMean (uniformWeight a) P val|
--         ≤ lam * (lam + 2 * q) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `NumberTheory/SmoothnessDispersionDecay.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/NumberTheory/SmoothnessDispersionDecay.lean#L208

-- Thm stub generated from NumberTheory/SmoothnessDispersionDecay.lean
import Mathlib
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion
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



/-! ### Specialisation to the smoothness of `x² − N` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ScaleSmoothness.smoothness_dispersion_decays(a : ι → ℕ) [∀ i, Fact (a i).Prime]
    (hodd : ∀ i, a i ≠ 2) (hinj : Function.Injective a) {K : Type*} [Fintype K]
    (P : (∀ i, ZMod (a i)) → K → ℚ) (val : K → ℚ) (lam q : ℚ)
    (hlam : 0 ≤ lam) (hq : 0 ≤ q)
    (hP : ∀ N, ∑ k, P N k = 1)
    (hmean : ∀ N, condMean P val N = lam * structureCorrection a N)
    (hvar : ∀ N, condVar P val N = lam * structureCorrection a N
      * (1 - q * structureCorrection a N)) :
    |mixVar (uniformWeight a) P val - mixMean (uniformWeight a) P val|
      ≤ lam * (lam + 2 * q) := by sorry
