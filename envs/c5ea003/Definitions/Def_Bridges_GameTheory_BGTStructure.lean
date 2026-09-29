-- Prove2me | Definitions.Def_Bridges_GameTheory_BGTStructure
-- name    : Bridges_GameTheory_BGTStructure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:21:59.955826+00:00
-- url     : https://prove2.me/theorems/a7b41ecb-273c-4b03-b536-cb7c7c5c998b
-- title:
--   Aether Catalog definitions — Bridges_GameTheory_BGTStructure
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GameTheory.BGTStructure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GameTheory/BGTStructure.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Breuillard–Green–Tao Structure Theorem: The K ≈ 1 Regime

This file establishes the first formal inverse theorems for product growth
in finite groups, specializing to the model case of `SL(2, 𝔽_p)`. The central
results prove that exact tripling rigidity (`|A³| = |A|`) forces subgroup
structure, and that small tripling under a strict-growth gap hypothesis forces
the set to be the entire group.

## Mathematical Context

The Breuillard–Green–Tao (BGT) structure theorem classifies approximate subgroups
of arbitrary groups. In the `K = 1` regime, the theorem becomes exact: a symmetric
set containing the identity with no tripling growth must be a subgroup. This file
formalizes this exact regime and the perturbative regime `K < 1 + δ` under a
strict-growth axiom.

## Main Definitions

* `ApproxSubgroupData` — structure encoding a symmetric set with identity
* `IsKApproxTripling` — predicate for K-approximate tripling
* `traceSet` — trace set of a subset of SL(2, 𝔽_p)

## Main Results

* `mul_self_eq_of_card_triple_eq` — |A³| = |A| implies A·A = A
* `subgroup_of_card_triple_eq_card` — exact tripling implies subgroup structure
* `eq_univ_of_card_triple_eq_card` — exact tripling + generation implies A = G
* `eq_univ_of_small_tripling_lt_gap` — small tripling under gap implies A = G
* `SL2_exact_tripling_generating_eq_univ` — SL₂ specialization

## Proof Architecture

The proofs follow **Strategy A** (cardinal rigidity → closure → subgroup):

1. From `1 ∈ A`, derive `A ⊆ A² ⊆ A³` (monotonicity of product towers).
2. From `|A³| = |A|` and step 1, deduce `A = A² = A³` by cardinality squeezing.
3. From `A² = A`, deduce multiplicative closure.
4. From closure + symmetry + identity, construct the subgroup.

**Strategy B** (strict growth contradiction) is used for the gap theorem:
the gap hypothesis directly contradicts small tripling for generating sets.

## References

* Breuillard, Green, Tao (2012). The structure of approximate groups.
* Helfgott (2008). Growth and generation in SL₂(ℤ/pℤ).
* Tao (2015). Expansion in finite simple groups of Lie type.
-/


open Finset Subgroup Pointwise

/-! ## Definitions -/


variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]



/-! ## Core Containment Lemmas -/





/-! ## The Rigidity Engine: Exact Tripling Forces Closure -/

/-
**Key rigidity lemma.** If `|A³| = |A|` and `1 ∈ A`, then `A * A = A`.
This is the engine of the exact inverse theorem: equal cardinality plus
containment forces equality at every level of the product tower.

*Proof.* From `1 ∈ A` we get `A ⊆ A² ⊆ A³`. Since `|A³| = |A|` and
`|A| ≤ |A²| ≤ |A³|`, all cardinalities are equal. Then `A ⊆ A²` with
`|A²| = |A|` forces `A = A²` by the finite pigeonhole principle.
-/


/-! ## Main Structure Theorems -/

/-
**Theorem 2: Exact tripling implies subgroup.**
If `A` is a finite symmetric subset containing `1` with `|A³| = |A|`,
then `A` is the carrier of a subgroup of `G`.

This is the exact inverse theorem at `K = 1`: the only symmetric sets
with no tripling growth are subgroups. The proof uses Strategy A:
cardinal rigidity forces `A = A²`, which gives multiplicative closure;
combined with symmetry and identity, this characterizes subgroups.
-/

/-
**Theorem 1: Exact tripling rigidity.**
If `A` is symmetric, contains `1`, generates `G`, and `|A³| = |A|`,
then `A` must be the entire group.

Combined with `subgroup_of_card_triple_eq_card`, this shows that the only
symmetric generating set with exact tripling in a finite group is `G` itself.
-/

/-
**Theorem 3: Near-rigidity under strict growth gap.**
If `G` satisfies a strict growth theorem with gap `δ > 0` — every symmetric
generating set that isn't all of `G` has `|A³| ≥ (1+δ)|A|` — then any
symmetric generating set with `|A³| < (1+δ)|A|` must be the entire group.

This is the formal nucleus of the perturbative BGT theorem: small tripling
plus generation forces saturation when a gap theorem is available.
-/

/-! ## SL₂(𝔽_p) Specialization -/

instance SL2_DecidableEq (p : ℕ) [Fact p.Prime] :
    DecidableEq (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
  Subtype.instDecidableEq

instance SL2_Fintype (p : ℕ) [Fact p.Prime] :
    Fintype (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :=
  Subtype.fintype _

/-
**Theorem 4: SL₂ exact tripling rigidity.**
For prime `p`, any symmetric subset of `SL(2, 𝔽_p)` containing the identity
that generates `SL(2, 𝔽_p)` and has exact tripling must be all of `SL(2, 𝔽_p)`.

This specializes the abstract rigidity theorem to the model case of
noncommutative growth theory.
-/

/-! ## Cross-Domain Bridge: Subgroup Closure from Exact Tripling -/

/-
**Cayley graph reachability from exact tripling.**
If `A` is symmetric with `1 ∈ A` and `|A³| = |A|`, then the subgroup
generated by `A` equals `A` (as sets). This means the connected component
of `1` in the Cayley graph with generators `A` is exactly the subgroup
corresponding to `A`.

This bridges product growth to graph connectivity: exact tripling means
the Cayley ball of radius 1 already exhausts its connected component.
-/

/-
**Product stabilization chain.**
If `|A³| = |A|` and `1 ∈ A`, then the entire product tower collapses:
`A = A² = A³ = A⁴ = ...`. This is the noncommutative analogue of the
abelian fact that `|A+A+A| = |A|` forces `kA = A` for all `k`.
-/

/-! ## Approximate Subgroup Analysis -/

/-- An **approximate subgroup report** summarizes the structural analysis
of a finite subset: whether it is a subgroup, its tripling ratio, and
the controlling subgroup if one exists. -/
structure ApproxSubgroupReport (G : Type*) [Group G] where
  /-- The original set -/
  carrier : Finset G
  /-- Cardinality of A -/
  cardA : ℕ
  /-- Cardinality of A² -/
  cardAA : ℕ
  /-- Cardinality of A³ -/
  cardAAA : ℕ
  /-- Whether 1 ∈ A -/
  hasOne : Bool
  /-- Whether A is symmetric -/
  isSymmetric : Bool
  /-- Whether A is multiplication-closed -/
  isMulClosed : Bool
  /-- Whether A is a subgroup carrier -/
  isSubgroup : Bool

/-- Compute the approximate subgroup report for a finite subset. -/
def analyzeApproxSubgroup (A : Finset G) : ApproxSubgroupReport G where
  carrier := A
  cardA := A.card
  cardAA := (A * A).card
  cardAAA := (A * A * A).card
  hasOne := decide ((1 : G) ∈ A)
  isSymmetric := decide (∀ g ∈ A, g⁻¹ ∈ A)
  isMulClosed := decide (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A)
  isSubgroup := decide ((1 : G) ∈ A) &&
    decide (∀ g ∈ A, g⁻¹ ∈ A) &&
    decide (∀ a ∈ A, ∀ b ∈ A, a * b ∈ A)

/-
The analyzer correctly reports subgroup status when exact tripling holds.
-/


