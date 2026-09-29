-- Prove2me | Definitions.Def_Bridges_CategoricalHellyPrinciple_HellyPrinciple
-- name    : Bridges_CategoricalHellyPrinciple_HellyPrinciple
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:16:58.963778+00:00
-- url     : https://prove2.me/theorems/1989d440-2a54-4e18-bd0f-3bd4b108d301
-- title:
--   Aether Catalog definitions — Bridges_CategoricalHellyPrinciple_HellyPrinciple
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.CategoricalHellyPrinciple.HellyPrinciple`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/CategoricalHellyPrinciple/HellyPrinciple.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harmonic Research
-/

/-!
# A Categorical Helly Principle for Probe Families

This file establishes a **local-to-global finite generation principle** for
probe-separated presheaves on finite discrete categories. The central idea is
that a separating probe family P of size k creates a "measurement window" of
bounded size: to control the global representable dimension of a presheaf F,
it suffices to check fiber sizes on subsets of size at most k + 1.

This is a categorical analogue of **Helly's theorem** from convex geometry.

## Main Definitions

* `restrictedRepDim` — the representable dimension restricted to a subset S.
* `Presheaf.LocallyRepFinGenUpTo` — locally representably finitely generated.
* `probeCapacity` — product of fiber sizes at probe objects.
* `categoricalHellyNumber` — the Helly number |P| + 1.
* `MinimalNonSeparatedWitness` — obstruction witness.

## Main Results

* `fiber_le_probe_capacity` — fiber bound under separation. (**Theorem 1**)
* `repFinGen_of_local_on_helly_bound` — categorical Helly theorem. (**Theorem 2**)
* `separation_supset_presheaf` — separation preserved by enlargement. (**Theorem 3**)
* `obstruction_localized_to_helly_number` — obstruction localization. (**Theorem 4**)
-/

open Finset Fintype CategoryTheory

noncomputable section

universe u v

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

variable {Ob : Type u} [Fintype Ob] [DecidableEq Ob]

/-! ### Inherited Definitions (from ProbeComplexity.RepresentableDimension) -/

/-- A probe family for the discrete presheaf model. -/
abbrev ObProbeFamilyH (Ob : Type u) := Finset Ob

/-- The probe signature of an element `x ∈ F(Y)` records its image under
restriction maps `r Y Z` for each probe object `Z ∈ P`. -/
def probeSignatureH
    {F : Ob → Type v} [∀ Y, Fintype (F Y)]
    (P : ObProbeFamilyH Ob)
    (r : ∀ Y Z, F Y → F Z)
    (Y : Ob) (x : F Y) : ∀ Z : ↥P, F (↑Z) :=
  fun ⟨Z, _⟩ => r Y Z x

/-- The probe signature map is injective at object Y. -/
def ProbeSignatureInjectiveH
    {F : Ob → Type v} [∀ Y, Fintype (F Y)]
    (P : ObProbeFamilyH Ob)
    (r : ∀ Y Z, F Y → F Z)
    (Y : Ob) : Prop :=
  Function.Injective (probeSignatureH P r Y)

/-- A probe family separates a presheaf F if probe signatures are
injective at every object. -/
def PresheafProbeSeparatesH
    {F : Ob → Type v} [∀ Y, Fintype (F Y)]
    (P : ObProbeFamilyH Ob) (r : ∀ Y Z, F Y → F Z) : Prop :=
  ∀ Y, ProbeSignatureInjectiveH P r Y

/-- Total objectwise cardinality of a presheaf. -/
def objectwiseTotalCardH
    (F : Ob → Type v) [∀ Y, Fintype (F Y)] : ℕ :=
  ∑ Y : Ob, Fintype.card (F Y)

/-! ### New Definitions -/

/-- The **restricted representable dimension** on a subset S: the sum of
fiber cardinalities over objects in S. -/
def restrictedRepDim (F : Ob → Type v) [∀ Y, Fintype (F Y)]
    (S : Finset Ob) : ℕ :=
  S.sum fun Y => Fintype.card (F Y)

/-- A presheaf is **locally representably finitely generated up to k** with
bound n if every restriction to at most k objects has total fiber size ≤ n. -/
def Presheaf.LocallyRepFinGenUpTo
    (F : Ob → Type v) [∀ Y, Fintype (F Y)] (k n : ℕ) : Prop :=
  ∀ S : Finset Ob, S.card ≤ k → restrictedRepDim F S ≤ n

/-- The **probe capacity** of F w.r.t. P: the product of fiber sizes at
probe objects. Under separation, this bounds each individual fiber. -/
def probeCapacity
    (F : Ob → Type v) [∀ Y, Fintype (F Y)]
    (P : ObProbeFamilyH Ob) : ℕ :=
  ∏ Z : ↥P, Fintype.card (F ↑Z)

/-- The **categorical Helly number** of a probe family P is |P| + 1. -/
def categoricalHellyNumber (P : ObProbeFamilyH Ob) : ℕ := P.card + 1

/-- A **minimal non-separated witness** at object Y: a pair of distinct
elements with identical probe signatures. -/
def MinimalNonSeparatedWitness
    {F : Ob → Type v} [∀ Y, Fintype (F Y)]
    (P : ObProbeFamilyH Ob) (r : ∀ Y Z, F Y → F Z) (Y : Ob) : Prop :=
  ∃ (x y : F Y), x ≠ y ∧ probeSignatureH P r Y x = probeSignatureH P r Y y

/-! ### Helper Lemmas -/






/-
The probe capacity is bounded by n^|P| when each probe fiber is ≤ n.
-/

/-! ### Theorem 1: Fiber Capacity Bound -/

/-
**Theorem 1 (Fiber Capacity Bound — the Helly Engine).**

Under probe separation, each fiber |F(Y)| is bounded by the product
of fiber sizes at probe objects: |F(Y)| ≤ ∏_{Z ∈ P} |F(Z)|.
-/

/-! ### Theorem 2: The Categorical Helly Theorem -/


/-! ### Theorem 3: Monotonicity -/


/-! ### Theorem 4: Separation Preserved by Probe Enlargement -/

/-
**Separation Preserved by Probe Enlargement.**

If P separates F and Q ⊇ P, then Q also separates F.
Presheaf-level analogue of `ProbeFamily.IsSeparating.supset`.
-/

/-! ### Theorem 5: Helly Bound Strengthens with More Probes -/


/-! ### Obstruction Theory -/

/-
**Obstruction Localization.**

If P does not separate F, then there exists an object Y and a non-separated
pair, whose support is contained in {Y} ∪ P (size ≤ |P| + 1).
-/

/-
The support of a non-separation witness is bounded by the Helly number.
-/

/-! ### Global Bounds -/


/-
Under separation, the representable dimension is at most
|Ob| times the probe capacity.
-/

/-! ### Connection to Existing Theory -/



/-
When every fiber equals the probe capacity, the representable dimension
exactly equals |Ob| * probeCapacity.
-/

end


