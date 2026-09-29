-- Prove2me | Theorems.Thm_repFinGen_of_local_on_helly_bound
-- name    : repFinGen_of_local_on_helly_bound
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:35:13.748034+00:00
-- url     : https://prove2.me/theorems/d15465b1-6373-4936-b69e-fdf5447dc631
-- title:
--   Theorem 2 (The Categorical Helly Theorem).
-- statement:
--   **Theorem 2 (The Categorical Helly Theorem).**
--
--   If P separates F and every subset of Ob of size ≤ |P| + 1 has restricted
--   representable dimension ≤ n, then the global representable dimension is
--   at most |Ob| · n^|P|.
--
--   **Proof architecture:**
--   1. Each probe-object fiber |F(Z)| ≤ n (from local bound on singletons).
--   2. Probe capacity ∏_{Z ∈ P} |F(Z)| ≤ n^|P| (product of bounded terms).
--   3. Each fiber |F(Y)| ≤ n^|P| (from Theorem 1 + step 2).
--   4. Sum: ∑_Y |F(Y)| ≤ |Ob| · n^|P|.
--
--   ```lean
--   theorem repFinGen_of_local_on_helly_bound    {F : Ob → Type v} [∀ Y, Fintype (F Y)] [∀ Y, DecidableEq (F Y)]
--       (P : ObProbeFamilyH Ob) (r : ∀ Y Z, F Y → F Z)
--       [DecidableEq (∀ Z : ↥P, F ↑Z)]
--       (hsep : PresheafProbeSeparatesH P r)
--       (n : ℕ)
--       (hlocal : Presheaf.LocallyRepFinGenUpTo F (categoricalHellyNumber P) n) :
--       objectwiseTotalCardH F ≤ Fintype.card Ob * n ^ P.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/CategoricalHellyPrinciple/HellyPrinciple.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/CategoricalHellyPrinciple/HellyPrinciple.lean#L183

-- Thm stub generated from Bridges/CategoricalHellyPrinciple/HellyPrinciple.lean
import Mathlib
import Definitions.Def_Bridges_CategoricalHellyPrinciple_HellyPrinciple
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






/-! ### New Definitions -/






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

theorem repFinGen_of_local_on_helly_bound    {F : Ob → Type v} [∀ Y, Fintype (F Y)] [∀ Y, DecidableEq (F Y)]
    (P : ObProbeFamilyH Ob) (r : ∀ Y Z, F Y → F Z)
    [DecidableEq (∀ Z : ↥P, F ↑Z)]
    (hsep : PresheafProbeSeparatesH P r)
    (n : ℕ)
    (hlocal : Presheaf.LocallyRepFinGenUpTo F (categoricalHellyNumber P) n) :
    objectwiseTotalCardH F ≤ Fintype.card Ob * n ^ P.card := by sorry
