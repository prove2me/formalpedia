-- Prove2me | solution 1 for repFinGen_of_local_on_helly_bound
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:23:48.445168+00:00
-- url     : https://prove2.me/submissions/f7a42b1f-8d98-480b-891f-f79dc8eb8505

-- Sol generated from Bridges/CategoricalHellyPrinciple/HellyPrinciple.lean
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

/-- Restricted representable dimension on a singleton equals the fiber size. -/
theorem restrictedRepDim_singleton (F : Ob → Type v) [∀ Y, Fintype (F Y)]
    (Z : Ob) : restrictedRepDim F {Z} = Fintype.card (F Z) := by
  simp [restrictedRepDim]



/-- Each probe-object fiber is bounded by the local bound n. -/
theorem probe_fiber_le_of_local_bound
    {F : Ob → Type v} [∀ Y, Fintype (F Y)]
    (P : ObProbeFamilyH Ob) (n : ℕ)
    (hlocal : Presheaf.LocallyRepFinGenUpTo F (categoricalHellyNumber P) n)
    (Z : Ob) (hZ : Z ∈ P) :
    Fintype.card (F Z) ≤ n := by
  have h1 : ({Z} : Finset Ob).card ≤ categoricalHellyNumber P := by
    simp [categoricalHellyNumber]
  have h2 := hlocal {Z} h1
  rwa [restrictedRepDim_singleton] at h2


/-
The probe capacity is bounded by n^|P| when each probe fiber is ≤ n.
-/
theorem probe_capacity_le_pow
    {F : Ob → Type v} [∀ Y, Fintype (F Y)]
    (P : ObProbeFamilyH Ob) (n : ℕ)
    (hbound : ∀ Z : Ob, Z ∈ P → Fintype.card (F Z) ≤ n) :
    probeCapacity F P ≤ n ^ P.card := by
  convert Finset.prod_le_prod' fun Z hZ => hbound Z <| Finset.mem_coe.mp hZ;
  · refine' Finset.prod_bij ( fun x hx => x ) _ _ _ _ <;> simp +decide;
  · rw [ Finset.prod_const, Finset.card_eq_sum_ones ]

/-! ### Theorem 1: Fiber Capacity Bound -/

/-
**Theorem 1 (Fiber Capacity Bound — the Helly Engine).**

Under probe separation, each fiber |F(Y)| is bounded by the product
of fiber sizes at probe objects: |F(Y)| ≤ ∏_{Z ∈ P} |F(Z)|.
-/
theorem fiber_le_probe_capacity
    {F : Ob → Type v} [∀ Y, Fintype (F Y)] [∀ Y, DecidableEq (F Y)]
    (P : ObProbeFamilyH Ob) (r : ∀ Y Z, F Y → F Z)
    [DecidableEq (∀ Z : ↥P, F ↑Z)]
    (hsep : PresheafProbeSeparatesH P r) (Y : Ob) :
    Fintype.card (F Y) ≤ probeCapacity F P := by
  convert Fintype.card_le_of_injective _ ( hsep Y ) using 1;
  rw [ Fintype.card_pi ];
  rfl

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


theorem solution    {F : Ob → Type v} [∀ Y, Fintype (F Y)] [∀ Y, DecidableEq (F Y)]
    (P : ObProbeFamilyH Ob) (r : ∀ Y Z, F Y → F Z)
    [DecidableEq (∀ Z : ↥P, F ↑Z)]
    (hsep : PresheafProbeSeparatesH P r)
    (n : ℕ)
    (hlocal : Presheaf.LocallyRepFinGenUpTo F (categoricalHellyNumber P) n) :
    objectwiseTotalCardH F ≤ Fintype.card Ob * n ^ P.card := by
  have hprobe_bound : ∀ Z : Ob, Z ∈ P → Fintype.card (F Z) ≤ n :=
    fun Z hZ => probe_fiber_le_of_local_bound P n hlocal Z hZ
  have hcap : probeCapacity F P ≤ n ^ P.card :=
    probe_capacity_le_pow P n hprobe_bound
  have hfiber : ∀ Y : Ob, Fintype.card (F Y) ≤ n ^ P.card :=
    fun Y => le_trans (fiber_le_probe_capacity P r hsep Y) hcap
  unfold objectwiseTotalCardH
  calc ∑ Y : Ob, Fintype.card (F Y)
      ≤ ∑ _Y : Ob, n ^ P.card :=
        Finset.sum_le_sum (fun Y _ => hfiber Y)
    _ = Fintype.card Ob * n ^ P.card := by
        simp [Finset.sum_const, Finset.card_univ]
