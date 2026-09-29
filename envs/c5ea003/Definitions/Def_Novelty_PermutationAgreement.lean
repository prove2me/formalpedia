-- Prove2me | Definitions.Def_Novelty_PermutationAgreement
-- name    : Novelty_PermutationAgreement
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:35:16.14254+00:00
-- url     : https://prove2.me/theorems/b6af39a7-e83e-4e52-b12b-86ef1d1db91d
-- title:
--   Aether Catalog definitions — Novelty_PermutationAgreement
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.PermutationAgreement`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/PermutationAgreement.lean by skeleton subtraction
import Mathlib

/-!
# Agreement sets of permutations and the fixed-point bridge

This file develops the elementary combinatorial infrastructure behind the
Deza–Frankl theory of *intersecting families of permutations*, the permutation
analogue of the Erdős–Ko–Rado / Complete Intersection circle of ideas.

Two permutations `σ, τ` of `Fin n` **agree** at position `i` when `σ i = τ i`.
A family `F` of permutations is *intersecting* if every pair agrees somewhere.

The central observation (the **fixed-point bridge**) is that the set of
positions on which `σ` and `τ` agree is *exactly* the set of fixed points of
`σ⁻¹ * τ`.  Consequently a family is intersecting **iff** for every pair the
permutation `σ⁻¹ * τ` is not a derangement.  This translates the extremal
set-system language of Deza–Frankl (1977) and Kupavskii (2022) into the
group-theoretic language of derangements / fixed-point conditions.

## Main results
* `PermIntersecting.agreements_eq_fixed` — the agreement set of `σ, τ` equals the
  fixed-point set of `σ⁻¹ * τ`.
* `PermIntersecting.agreements_card` — the number of agreements equals
  `n - (σ⁻¹ * τ).support.card`.
* `PermIntersecting.isIntersecting_iff_no_derangement` — a family is intersecting
  iff every `σ⁻¹ * τ` has a fixed point.

-- !-- Lab Notes -- !--
## Hypothesis (Hypothesizer)
Conjecture: for permutations, "agreeing in a coordinate" is a *conjugation-free*
condition expressible purely through fixed points of a single derived
permutation `σ⁻¹τ`.  If true, all of intersecting-family theory for permutations
becomes derangement theory.

## Experiment (Experimenter)
Checked on `S₃`: `σ = (1 2 3)`, `τ = (1 3 2)`.  `σ⁻¹τ = (1 3 2)(1 2 3)` — has no
fixed point, and indeed `σ, τ` disagree everywhere.  For `σ = id`, agreements
with any `τ` are the fixed points of `τ`, matching the bridge.

## Analysis (Analyst)
The bridge is a *pointwise* equivalence `σ i = τ i ↔ (σ⁻¹τ) i = i`, hence lifts
to equality of finsets and then to cardinalities via the support complement.
This is robust: no size/uniformity hypotheses are needed.

## Critique (Critic)
Guarded against vacuity: `IsIntersecting` uses `Nonempty` of the agreement set,
not a bare existential over an empty type; for `n = 0` all statements remain
meaningful (every permutation is `1`).

## Synthesis (Principal Investigator)
The fixed-point bridge is the correct primitive: it converts every statement
about coordinate-agreement of permutations into a statement about fixed points
(equivalently, derangements) of a single derived permutation.  This is the exact
hinge that lets the set-system Complete Intersection Theorem be transported to
the symmetric group, and it is the foundation reused in
`PermutationCompleteIntersection`.
-/

open Equiv Function Finset

namespace PermIntersecting

variable {n : ℕ}

/-- The set of positions on which two permutations agree. -/
def agreements (σ τ : Perm (Fin n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => σ i = τ i)

/-- A family of permutations is *intersecting* if any two members agree in at
least one coordinate. -/
def IsIntersecting (F : Finset (Perm (Fin n))) : Prop :=
  ∀ σ ∈ F, ∀ τ ∈ F, (agreements σ τ).Nonempty


/-
**Fixed-point bridge (pointwise).** `σ` and `τ` agree at `i` iff `σ⁻¹τ`
fixes `i`.
-/

/-
**Fixed-point bridge (as finsets).** The agreement set of `σ` and `τ` equals
the fixed-point set of `σ⁻¹ * τ`.
-/

/-
The number of agreements of `σ` and `τ` equals `n` minus the size of the
support of `σ⁻¹ * τ`.
-/

/-
**Intersecting ⟺ no derangements.** A family is intersecting iff for every
pair the permutation `σ⁻¹ * τ` has a fixed point (is not a derangement).
-/

end PermIntersecting


