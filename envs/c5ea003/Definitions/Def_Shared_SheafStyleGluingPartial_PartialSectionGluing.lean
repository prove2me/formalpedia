-- Prove2me | Definitions.Def_Shared_SheafStyleGluingPartial_PartialSectionGluing
-- name    : Shared_SheafStyleGluingPartial_PartialSectionGluing
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:36:12.660585+00:00
-- url     : https://prove2.me/theorems/0ca22385-a7bd-4c4b-9ca5-ac7ee86c2f42
-- title:
--   Aether Catalog definitions — Shared_SheafStyleGluingPartial_PartialSectionGluing
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.SheafStyleGluingPartial.PartialSectionGluing`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/SheafStyleGluingPartial/PartialSectionGluing.lean by skeleton subtraction
import Mathlib

/-!
# Sheaf-style gluing for partial sections

This file develops an elementary, sheaf-flavoured theory of *partial sections*
`PartialSection ι α := ι → Option α`.  Intuitively a partial section is a
database row whose fields (indexed by `ι`) may or may not be filled in.

We define the notions of `Support`, `Compatible`, `Extends`, `glue` (binary
gluing) and `familyGlue` (gluing of an arbitrary compatible family), and prove
the basic sheaf axioms: locality (a section is determined by its restrictions)
and gluing (compatible sections can be glued, uniquely on the union of their
supports).

The development is deliberately elementary and avoids category theory.
-/

universe u v w

/-- A partial section assigns to each index `i : ι` an optional value in `α`. -/
def PartialSection (ι : Type u) (α : Type v) : Type (max u v) := ι → Option α

namespace PartialSection

variable {ι : Type u} {α : Type v} {κ : Type w}
variable {f g h : PartialSection ι α} {i : ι} {a : α}

/-- The support of a partial section: the indices where it is defined. -/
def Support (f : PartialSection ι α) : Set ι := {i | f i ≠ none}

/-- Two partial sections are compatible if they agree wherever both are defined. -/
def Compatible (f g : PartialSection ι α) : Prop :=
  ∀ i, f i ≠ none → g i ≠ none → f i = g i

/-- `Extends g f` means `g` agrees with `f` wherever `f` is defined. -/
def Extends (g f : PartialSection ι α) : Prop :=
  ∀ i, f i ≠ none → g i = f i

/-- Binary gluing: take `f`'s value where it is defined, otherwise `g`'s. -/
def glue (f g : PartialSection ι α) : PartialSection ι α :=
  fun i => match f i with
    | some a => some a
    | none => g i

/-- 1. Membership in the support. -/
theorem not_mem_support_iff : i ∉ f.Support ↔ f i = none := by
  unfold Support
  simp only [Set.mem_setOf_eq, not_not]

/-- 2. On the support there is an actual value. -/
theorem exists_of_mem_support : i ∈ f.Support → ∃ a, f i = some a := by
  intro hi
  unfold Support at hi
  simp only [Set.mem_setOf_eq] at hi
  exact Option.ne_none_iff_exists'.1 hi

/-- 3. Compatibility is reflexive. -/
theorem compatible_refl : Compatible f f := by
  intro i _ _; rfl

/-- 4. Compatibility is symmetric. -/
theorem compatible_symm : Compatible f g → Compatible g f := by
  intro hfg i hgi hfi
  exact (hfg i hfi hgi).symm

/-- 5. Pointwise description of `glue`. -/
theorem glue_apply : (glue f g) i = if f i ≠ none then f i else g i := by
  unfold glue
  cases hfi : f i with
  | none => simp
  | some a => simp

/-- 6. `glue` keeps `f`'s value where `f` is defined. -/
theorem glue_eq_left_of_some : f i = some a → (glue f g) i = some a := by
  intro hfi
  unfold glue
  rw [hfi]

/-- 7. `glue` falls back to `g` where `f` is undefined. -/
theorem glue_eq_right_of_none : f i = none → (glue f g) i = g i := by
  intro hfi
  unfold glue
  rw [hfi]

/-- 8. The support of a glued section is the union of supports.

The compatibility hypothesis `Compatible f g` is requested in the statement but
turns out to be unnecessary for the proof, so it is named `_hc`. -/
theorem support_glue_eq_union (_hc : Compatible f g) :
    (glue f g).Support = f.Support ∪ g.Support := by
  ext i
  unfold Support
  simp only [Set.mem_setOf_eq, Set.mem_union]
  constructor
  · intro hgl
    cases hfi : f i with
    | some a => left; exact Option.some_ne_none a
    | none =>
      right
      rw [glue_eq_right_of_none hfi] at hgl
      exact hgl
  · intro hor
    cases hfi : f i with
    | some a => rw [glue_eq_left_of_some hfi]; exact Option.some_ne_none a
    | none =>
      rw [glue_eq_right_of_none hfi]
      rcases hor with hf | hg
      · exact absurd hfi hf
      · exact hg

/-- 9. `glue f g` extends `f`. -/
theorem glue_extends_left : Extends (glue f g) f := by
  intro i hfi
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hfi
  rw [glue_eq_left_of_some ha, ha]

/-- 10. If `f` and `g` are compatible, `glue f g` extends `g` too. -/
theorem glue_extends_right (hc : Compatible f g) : Extends (glue f g) g := by
  intro i hgi
  by_cases hfi : f i = none
  · rw [glue_eq_right_of_none hfi]
  · obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 hfi
    rw [glue_eq_left_of_some ha, ← ha]
    exact hc i hfi hgi

/-- 11. Two sections with a common extension are compatible. -/
theorem compatible_of_common_extension (hf : Extends h f) (hg : Extends h g) :
    Compatible f g := by
  intro i hfi hgi
  rw [← hf i hfi, hg i hgi]

/-- 12. Compatibility is equivalent to having a common extension. -/
theorem compatible_iff_exists_common_extension :
    Compatible f g ↔ ∃ h, Extends h f ∧ Extends h g := by
  constructor
  · intro hc
    exact ⟨glue f g, glue_extends_left, glue_extends_right hc⟩
  · rintro ⟨h, hf, hg⟩
    exact compatible_of_common_extension hf hg

/-- 13. Locality: a section is determined by mutual extension. -/
theorem restrict_locality (hfg : Extends f g) (hgf : Extends g f) : f = g := by
  funext i
  by_cases hfi : f i = none
  · by_cases hgi : g i = none
    · rw [hfi, hgi]
    · exact hfg i hgi
  · exact (hgf i hfi).symm

/-- 14. Uniqueness of the glued section on the union of supports.

The compatibility hypothesis `Compatible f g` is requested in the statement but
turns out to be unnecessary for the proof, so it is named `_hc`. -/
theorem glue_unique (_hc : Compatible f g) :
    ∀ h, Extends h f → Extends h g → h.Support ⊆ f.Support ∪ g.Support →
      h = glue f g := by
  intro h hf hg hsupp
  funext i
  cases hfi : f i with
  | some a =>
    rw [glue_eq_left_of_some hfi]
    have : f i ≠ none := by rw [hfi]; exact Option.some_ne_none a
    rw [hf i this, hfi]
  | none =>
    rw [glue_eq_right_of_none hfi]
    cases hgi : g i with
    | some b =>
      have : g i ≠ none := by rw [hgi]; exact Option.some_ne_none b
      rw [hg i this, hgi]
    | none =>
      by_contra hne
      have hi : i ∈ h.Support := by
        unfold Support; simp only [Set.mem_setOf_eq]
        exact hne
      rcases hsupp hi with hf' | hg'
      · unfold Support at hf'; simp only [Set.mem_setOf_eq] at hf'
        exact hf' hfi
      · unfold Support at hg'; simp only [Set.mem_setOf_eq] at hg'
        exact hg' hgi

/-- A family of partial sections is pairwise compatible. -/
def PairwiseCompatible (s : κ → PartialSection ι α) : Prop :=
  ∀ j k, Compatible (s j) (s k)

open Classical in
/-- Gluing of an arbitrary family of partial sections: at each index take the
value of some member of the family that is defined there, if any. -/
noncomputable def familyGlue (s : κ → PartialSection ι α) : PartialSection ι α :=
  fun i => if h : ∃ j, s j i ≠ none then s (Classical.choose h) i else none

/-- 15. The family glue extends every member of a pairwise compatible family. -/
theorem familyGlue_extends {s : κ → PartialSection ι α}
    (hc : PairwiseCompatible s) : ∀ j, Extends (familyGlue s) (s j) := by
  classical
  intro j i hji
  unfold familyGlue
  have hex : ∃ k, s k i ≠ none := ⟨j, hji⟩
  rw [dif_pos hex]
  exact hc (Classical.choose hex) j i (Classical.choose_spec hex) hji

/-- 16. Existence of a common extension for a pairwise compatible family. -/
theorem glue_family_exists {s : κ → PartialSection ι α}
    (hc : PairwiseCompatible s) : ∃ h, ∀ j, Extends h (s j) :=
  ⟨familyGlue s, familyGlue_extends hc⟩

end PartialSection


