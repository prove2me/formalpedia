-- Prove2me | Definitions.Def_Applications_PositionalStratumMeasure
-- name    : Applications_PositionalStratumMeasure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:55:04.370562+00:00
-- url     : https://prove2.me/theorems/f6520f89-4bb4-4060-928f-15ea6a30269b
-- title:
--   Aether Catalog definitions — Applications_PositionalStratumMeasure
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.PositionalStratumMeasure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/PositionalStratumMeasure.lean by skeleton subtraction
import Mathlib
/-
# Positional-stratum measure framework (GAP-L4)

A self-contained finite-measure framework for *positional strata* in one-shot
search / retrieval cost models.

The setting is elementary but the statements are the ones that carry the load:

* `positions M` — the ranked slots `1, …, M`;
* a *weight* `w : ℕ → ℝ`, the probability of the target sitting at a given slot;
* a *cost kernel* `c : ℕ → ℝ`, the number of probes charged when the target is resolved
  at that slot.  Two kernels matter: the **scan kernel** `c i = i` (sequential probing)
  and the **block-commitment kernel** (constant on each stratum), which is the one behind
  the certified law of `PositionalStratumCertifiedLaw`.

Main results.

* `rbar_identity` : the universal object,  `EC = P · r̄_R + (1 - P) · r̄_C`, an *exact*
  identity for every weight, every cost kernel and every stratum of nondegenerate mass.
* `theta_eq_one_of_uniform` / `uniform_of_forall_theta_eq_one` : the booking factor
  `Θ = r̄_R / (cell centre)` equals `1` on uniform cells, and if it equals `1` on
  *every* cell then the weight is uniform.  The single-cell converse is **false**:
  `theta_eq_one_not_uniform` is an explicit non-uniform witness with `Θ = 1`.
* `scan_cost_le_baseline` : the majorization / Chebyshev step — a descending (antitone)
  weight has expected scan cost at most the full-scan baseline `C₀ = (M+1)/2`.
* `exchange_inequality`, `sorted_le_of_antitone` : the rearrangement step.
* `exists_large_bucket`, `speedup_le_two_pow_kbits` : the `k_bits` (pigeonhole) branch.
* `master_inequality`, `master_inequality_of_filter` :
  `S ≤ min (1/(Λ·Θ·q̂)) (2^k/(Λ·Θ))`.
* `value_universality_fails` : the booked (uniform-cell) value law is **not** universal —
  off uniform cells the true speedup exceeds the booked one by an *unbounded* factor.
-/

namespace PositionalStratum

open Finset

noncomputable section

/-! ## The finite positional space -/

/-- The ranked slots `1, …, M`. -/
def positions (M : ℕ) : Finset ℕ := Finset.Icc 1 M

/-- Total mass of a weight on a stratum. -/
def mass (R : Finset ℕ) (w : ℕ → ℝ) : ℝ := ∑ i ∈ R, w i

/-- Expected cost of the algorithm: cost kernel `c` averaged against the weight `w`. -/
def EC (M : ℕ) (c w : ℕ → ℝ) : ℝ := ∑ i ∈ positions M, c i * w i

/-- Conditional mean cost inside a stratum, `r̄_R`. -/
def rbar (R : Finset ℕ) (c w : ℕ → ℝ) : ℝ := (∑ i ∈ R, c i * w i) / mass R w

/-- The (unweighted) centre of a stratum for the cost kernel `c`. -/
def cellCentre (R : Finset ℕ) (c : ℕ → ℝ) : ℝ := (∑ i ∈ R, c i) / R.card

/-- The booking factor `Θ = r̄_R / centre(R)`: it measures how far the weight is from
uniform *inside* the stratum. -/
def Theta (R : Finset ℕ) (c w : ℕ → ℝ) : ℝ := rbar R c w / cellCentre R c

/-- The scan cost kernel: resolving at slot `i` costs `i` probes. -/
def scanCost (i : ℕ) : ℝ := (i : ℝ)

/-- The full-scan baseline cost `C₀ = (M+1)/2` (mean position under the uniform weight). -/
def baselineC0 (M : ℕ) : ℝ := ((M : ℝ) + 1) / 2




/-! ## The r̄-identity : the universal object -/



/-! ## The booking factor `Θ` : uniformity detection -/




/-! ## Majorization : the descending weight beats the baseline -/





/-! ## The `k_bits` branch : pigeonhole on the filter -/



/-! ## The master inequality -/



/-! ## Off uniform cells the *value* law is not universal -/




/-- The booked (uniform-within-cell) expected scan cost for a head stratum of size `m`
inside `M` slots with capture probability `P`. -/
def bookedEC (M m : ℕ) (P : ℝ) : ℝ :=
  P * (((m : ℝ) + 1) / 2) + (1 - P) * ((m : ℝ) + ((M : ℝ) - m + 1) / 2)

/-- The adversarial witness family: all the captured mass sits at the very head of the
stratum and all the escaping mass at the very head of the complement. -/
def headWitness (m : ℕ) : ℕ → ℝ :=
  fun i => if i = 1 then 1 - 1 / (m : ℝ) else if i = m + 1 then 1 / (m : ℝ) else 0








end

end PositionalStratum


