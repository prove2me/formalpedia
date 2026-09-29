-- Prove2me | solution 1 for ScaleSmoothness.dispersion_index_sub_one_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:22:54.994152+00:00
-- url     : https://prove2.me/submissions/c7e87f45-9b03-4f86-b4b4-861e114dd05a

-- Sol generated from NumberTheory/SmoothnessDispersionDecay.lean
import Mathlib
import Definitions.Def_NumberTheory_SmoothnessDispersionDecay
import Theorems.Thm_ScaleSmoothness_mixVar_eq

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








/-! ### Non-vacuity: a single-trial Bernoulli realisation of the model -/

open BernoulliWitness

variable (a : ι → ℕ) [∀ i, Fact (a i).Prime] (q : ℚ)









open ScaleSmoothness in
theorem solution(w : Ω → ℚ) (P : Ω → K → ℚ) (val : K → ℚ)
    (C : Ω → ℚ) (lam q : ℚ) (hlam : 0 ≤ lam)
    (hP : ∀ ω, ∑ k, P ω k = 1) (hw : ∑ ω, w ω = 1) (hC : ∑ ω, w ω * C ω = 1)
    (hmean : ∀ ω, condMean P val ω = lam * C ω)
    (hvar : ∀ ω, condVar P val ω = lam * C ω * (1 - q * C ω))
    (S₂ : ℚ) (hS₂ : ∑ ω, w ω * (C ω) ^ 2 = S₂) (hq : 0 ≤ q) (hS₂1 : 1 ≤ S₂) :
    |mixVar w P val - mixMean w P val| ≤ lam * (lam * (S₂ - 1) + q * S₂) := by
  obtain ⟨hM, hV⟩ := mixVar_eq w P val C lam q hP hw hC hmean hvar
  rw [hM, hV, hS₂]
  have hdiff : lam * (1 + lam * (S₂ - 1) - q * S₂) - lam
      = lam * (lam * (S₂ - 1) - q * S₂) := by ring
  rw [hdiff, abs_mul, abs_of_nonneg hlam]
  have hbound : |lam * (S₂ - 1) - q * S₂| ≤ lam * (S₂ - 1) + q * S₂ := by
    have h1 : 0 ≤ lam * (S₂ - 1) := mul_nonneg hlam (by linarith)
    have h2 : 0 ≤ q * S₂ := mul_nonneg hq (by linarith)
    rw [abs_le]
    constructor <;> linarith
  exact mul_le_mul_of_nonneg_left hbound hlam
