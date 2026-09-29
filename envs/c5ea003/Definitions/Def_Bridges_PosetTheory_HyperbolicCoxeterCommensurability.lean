-- Prove2me | Definitions.Def_Bridges_PosetTheory_HyperbolicCoxeterCommensurability
-- name    : Bridges_PosetTheory_HyperbolicCoxeterCommensurability
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:31:59.433023+00:00
-- url     : https://prove2.me/theorems/5dddade4-fb55-457b-9f87-5cb69e3ded62
-- title:
--   Aether Catalog definitions — Bridges_PosetTheory_HyperbolicCoxeterCommensurability
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.PosetTheory.HyperbolicCoxeterCommensurability`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/PosetTheory/HyperbolicCoxeterCommensurability.lean by skeleton subtraction
import Mathlib
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

namespace HyperbolicCoxeterCommensurability

open Classical

/-! ## The commensurability-counting bridge -/



/-! ## The Gram-matrix range constraint -/


/-! ## A non-degenerate model exhibiting exponential growth

The model polytope type is `(Fin n → Bool) × Bool`.  The first component encodes a
"combinatorial type" separated by the commensurability invariant; the second
component is a *decoration* that commensurability cannot see, ensuring the relation
is strictly coarser than equality. -/

/-- Commensurability in the model: agreement of the first (combinatorial) component,
ignoring the decoration bit. -/
def modelSetoid (n : ℕ) : Setoid ((Fin n → Bool) × Bool) where
  r p q := p.1 = q.1
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h1 h2 => h1.trans h2⟩

/-- The separating commensurability invariant: the combinatorial type. -/
def modelInv (n : ℕ) (p : (Fin n → Bool) × Bool) : Fin n → Bool := p.1

/-- Volume of a model polytope: the number of occupied coordinates.  It is bounded
by `n`, so it grows only linearly while the number of classes grows as `2 ^ n`. -/
noncomputable def modelVol (n : ℕ) (p : (Fin n → Bool) × Bool) : ℝ :=
  ((Finset.univ.filter (fun i => p.1 i = true)).card : ℝ)





/-! ## Main result: exponential growth of commensurability classes in volume -/


end HyperbolicCoxeterCommensurability


