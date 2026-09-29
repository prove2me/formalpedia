-- Prove2me | Theorems.Thm_HyperbolicCoxeterCommensurability_gram_offdiagonal_mem_Ioc
-- name    : HyperbolicCoxeterCommensurability.gram_offdiagonal_mem_Ioc
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:49:24.762958+00:00
-- url     : https://prove2.me/theorems/df4bd17f-b4a5-4c41-b02d-adf12833fd71
-- title:
--   Admissible off-diagonal Gram entry.
-- statement:
--   **Admissible off-diagonal Gram entry.**  For two facets of a hyperbolic
--   Coxeter polytope meeting at dihedral angle `π / m` with `m ≥ 2`, the corresponding
--   off-diagonal Gram-matrix entry `-cos(π / m)` lies in the half-open interval
--   `(-1, 0]`.  Equivalently, `cos(π / m) ∈ [0, 1)`.
--
--   ```lean
--   theorem HyperbolicCoxeterCommensurability.gram_offdiagonal_mem_Ioc(m : ℕ) (hm : 2 ≤ m) :
--       -1 < -Real.cos (Real.pi / m) ∧ -Real.cos (Real.pi / m) ≤ 0 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/HyperbolicCoxeterCommensurability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/HyperbolicCoxeterCommensurability.lean#L112

-- Thm stub generated from Bridges/PosetTheory/HyperbolicCoxeterCommensurability.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_HyperbolicCoxeterCommensurability
/-!
# Commensurability invariants and exponential growth of commensurability classes

This file formalizes the combinatorial-arithmetic engine behind the classification
and *incommensurability* results for finite-volume hyperbolic Coxeter polytopes,
in the spirit of the classification of five-dimensional Coxeter polytopes with
eight facets and the Bogachev–Douba–Raimbault style construction of infinitely
many pairwise incommensurable noncompact Coxeter polytopes whose number of
commensurability classes grows at least exponentially in volume.

We isolate the two structural ingredients that make such a growth statement work
and prove them cleanly, then combine them in a non-degenerate concrete model.

## The commensurability-counting bridge

Commensurability is an equivalence relation on hyperbolic orbifolds; two Coxeter
polytopes are commensurable when their reflection groups share a finite-index
subgroup up to conjugacy.  A *commensurability invariant* is any quantity
(maximal cusp density, invariant trace field, covolume ratios, …) that is constant
on commensurability classes.  The elementary but decisive observation is:

> The number of distinct values taken by a commensurability invariant on a family
> is a lower bound for the number of commensurability classes in that family.

This is `card_image_invariant_le` / `num_classes_ge_of_invariant`.  It converts a
*geometric* separation problem (are these polytopes pairwise incommensurable?)
into a *combinatorial* counting problem (how many invariant values occur?).

## The Gram-matrix range constraint

For a hyperbolic Coxeter polytope the Gram matrix of its outward normals has
diagonal entries `1` and off-diagonal entries `-cos(π / m)` where `m ≥ 2` is the
order of the dihedral angle between two facets meeting at angle `π / m`.  We prove
the range constraint `-1 < -cos(π / m) ≤ 0`, the analytic fact underlying the
admissibility of a Coxeter diagram (`gram_offdiagonal_mem_Ioc`).

## Exponential growth in volume

Combining the counting bridge with an explicit family whose volume grows linearly
while a genuine (non-trivial) commensurability invariant separates `2 ^ n`
members, we obtain `exponential_growth_in_volume`: a family of bounded volume with
at least `2 ^ n` commensurability classes.  The commensurability relation in the
model is strictly coarser than equality (its classes have size two), so the bound
is not a bookkeeping artefact of using the discrete relation.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The headline "number of commensurability classes grows
  at least exponentially in volume" is not intrinsically geometric — it factors
  through (a) a separating invariant and (b) a linear-volume / exponential-count
  family.  Conjecture: (a) is a one-line card-of-image inequality and (b) can be
  realised with a commensurability relation that is provably coarser than equality.
Experiment (Experimenter): Proved the invariant inequality via factorisation of
  the invariant through the quotient map (`Finset.image_image` + `card_image_le`).
  Built the Gram off-diagonal range from strict antitonicity of `cos` on `[0, π]`.
  Realised the family on `(Fin n → Bool) × Bool` with a "decoration" bit invisible
  to commensurability, giving classes of size exactly two.
Analysis (Analyst): The invariant bound is tight and dimension-free; the geometric
  content (that maximal cusp density really is a commensurability invariant taking
  many values) is exactly the input we take as a hypothesis in the abstract theorem
  and realise honestly in the model.  Failure mode avoided: taking the invariant to
  be the identity would force commensurability = equality (degenerate); the
  decoration bit prevents this.
Critique (Critic): Checked that the model relation is a genuine equivalence with
  non-singleton classes (`modelSetoid_not_discrete`), that the value count is
  exactly `2 ^ n` (not an over-count), and that the volume bound is linear.  No
  theorem is vacuous or proved by `decide`/`native_decide`.
Synthesis (PI): The exponential-growth phenomenon is a corollary of one counting
  inequality plus one explicit family; the hyperbolic geometry enters only through
  the *existence* of a separating invariant, cleanly isolated as a hypothesis.
-/

open HyperbolicCoxeterCommensurability

open Classical

/-! ## The commensurability-counting bridge -/



/-! ## The Gram-matrix range constraint -/

theorem HyperbolicCoxeterCommensurability.gram_offdiagonal_mem_Ioc(m : ℕ) (hm : 2 ≤ m) :
    -1 < -Real.cos (Real.pi / m) ∧ -Real.cos (Real.pi / m) ≤ 0 := by sorry
