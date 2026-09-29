-- Prove2me | Definitions.Def_NumberTheory_SmoothnessDispersionDecay
-- name    : NumberTheory_SmoothnessDispersionDecay
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:35.182017+00:00
-- url     : https://prove2.me/theorems/527b079f-6b27-4798-abc0-291f35ee271a
-- title:
--   Aether Catalog definitions — NumberTheory_SmoothnessDispersionDecay
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.SmoothnessDispersionDecay`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/SmoothnessDispersionDecay.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_ScaleSmoothnessDispersion

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

namespace ScaleSmoothness

open Finset

/-! ### A finite law of total variance -/

variable {Ω : Type*} [Fintype Ω] {K : Type*} [Fintype K]

/-- Conditional mean of the value `val` under the conditional distribution `P ω`. -/
def condMean (P : Ω → K → ℚ) (val : K → ℚ) (ω : Ω) : ℚ := ∑ k, P ω k * val k

/-- Conditional variance of `val` under `P ω`. -/
def condVar (P : Ω → K → ℚ) (val : K → ℚ) (ω : Ω) : ℚ :=
  ∑ k, P ω k * (val k - condMean P val ω) ^ 2

/-- Mean of the mixture with weights `w`. -/
def mixMean (w : Ω → ℚ) (P : Ω → K → ℚ) (val : K → ℚ) : ℚ :=
  ∑ ω, w ω * condMean P val ω

/-- Variance of the mixture with weights `w`. -/
def mixVar (w : Ω → ℚ) (P : Ω → K → ℚ) (val : K → ℚ) : ℚ :=
  ∑ ω, w ω * ∑ k, P ω k * (val k - mixMean w P val) ^ 2


/-! ### The dispersion identity for a mixed count model -/



/-! ### Specialisation to the smoothness of `x² − N` -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The uniform weights on the residue data of the prime family `a`. -/
noncomputable def uniformWeight (a : ι → ℕ) : (∀ i, ZMod (a i)) → ℚ :=
  fun _ => 1 / ∏ i, (a i : ℚ)







/-! ### Non-vacuity: a single-trial Bernoulli realisation of the model -/

namespace BernoulliWitness

variable (a : ι → ℕ) [∀ i, Fact (a i).Prime] (q : ℚ)

/-- The conditional law of a single trial with success probability
`q · C(N)`. -/
def P (N : ∀ i, ZMod (a i)) : Bool → ℚ :=
  fun b => if b then q * structureCorrection a N else 1 - q * structureCorrection a N

/-- The value of a single trial: `1` on success, `0` on failure. -/
def val : Bool → ℚ := fun b => if b then 1 else 0





end BernoulliWitness

end ScaleSmoothness


