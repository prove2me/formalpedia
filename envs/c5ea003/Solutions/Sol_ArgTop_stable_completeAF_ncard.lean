-- Prove2me | solution 1 for ArgTop.stable_completeAF_ncard
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T19:11:40.893411+00:00
-- url     : https://prove2.me/submissions/cf43ffae-fa08-4813-957b-7c302b3b62b8

-- Thm stub generated from Novelty/ArgumentationStable.lean
import Mathlib
import Definitions.Def_Novelty_ArgumentationStable

/-!
# The topology of argumentation, V: stable extensions and the stable/preferred/Euler chain

This file is **self-contained** (it re-declares the basic Dung semantics) and
deepens the theory begun in `ArgumentationCore`, `ArgumentationExtensions`,
`ArgumentationSimplicial` and `ArgumentationSymmetric` by developing the
strongest of the classical *extension-based* semantics — the **stable
extension** — and situating it inside the full hierarchy

  `stable ⟹ preferred ⟹ complete ⟹ admissible ⟹ conflict-free`.

A set `S` is a **stable extension** when it is conflict-free and *attacks every
argument it does not contain* (`∀ a ∉ S, ∃ b ∈ S, R b a`).  Stable extensions are
the "no abstention" positions: every argument is either accepted or explicitly
defeated.

## The chain of results

* `stable_defends`     — a stable set defends each of its members;
* `stable_admissible`  — every stable extension is admissible;
* `stable_complete`    — every stable extension is complete (closed under defense);
* `stable_preferred`   — **every stable extension is preferred** (maximal admissible);
* `stable_maximalConflictFree` — every stable extension is a *facet* of `K(AF)`;
* `groundedExt_subset_stable` — the grounded extension is contained in every
  stable extension (skeptical ⊆ every stable position).

## The symmetric bridge and the Euler correspondence

For **symmetric irreflexive** frameworks (the model of two-sided disagreement)
we prove the exact collapse

* `maximalConflictFree_stable_of_symmetric` and hence
* `stable_iff_preferred_of_symmetric_irrefl` — **stable = preferred = facet** of
  the conflict-free complex `K(AF)`.

Specialising to the **complete conflict graph** `completeAF n` (which is
symmetric and irreflexive) we obtain, entirely self-contained:

* `stable_completeAF_iff` — the stable extensions are exactly the singletons;
* `stable_completeAF_ncard` — there are exactly `n` of them;
* `euler_eq_stable_completeAF` — **the Euler characteristic of `K(AF)` equals the
  number of stable extensions** (for `n ≥ 1`), extending the Euler/semantics
  bridge of `ArgumentationSymmetric` from preferred to stable extensions.
-/

open ArgTop

-- open removed: section is not a namespace

variable {A : Type*} (R : A → A → Prop)

/-! ## Basic Dung semantics (self-contained) -/











/-! ## The stable hierarchy -/






/-! ## The grounded extension is below every stable extension -/





/-! ## Symmetric frameworks: stable = preferred = facet -/







/-! ## The complete conflict graph: stable count and the Euler bridge -/

open ArgTop

-- open removed: section is not a namespace

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem s_groundedExt_subset_of_charF_subset {A : Type*} (R : A → A → Prop) {S : Set A}
    (h : charF R S ⊆ S) : groundedExt R ⊆ S :=
  OrderHom.lfp_le _ h

theorem s_conflictFree_completeAF_iff (n : ℕ) (S : Set (Fin n)) :
    ConflictFree (completeAF n) S ↔ S.Subsingleton := by
  constructor
  · intro h a ha b hb
    by_contra hne
    exact h a ha b hb hne
  · intro h a ha b hb hab
    exact hab (h ha hb)

theorem s_maximalConflictFree_stable_of_symmetric {A : Type*} (R : A → A → Prop)
    (hsym : Symmetric R) (hirr : ∀ a, ¬ R a a) {S : Set A}
    (hS : MaximalConflictFree R S) : Stable R S := by
  obtain ⟨hcf, hmax⟩ := hS
  refine ⟨hcf, ?_⟩
  intro a haS
  by_contra hcon
  have hno : ∀ b ∈ S, ¬ R b a := fun b hb hba => hcon ⟨b, hb, hba⟩
  have hins : ConflictFree R (insert a S) := by
    intro x hx y hy hxy
    rcases Set.mem_insert_iff.1 hx with hxa | hx
    · rcases Set.mem_insert_iff.1 hy with hya | hy
      · exact hirr a (by rw [hxa, hya] at hxy; exact hxy)
      · exact hno y hy (hsym (show R a y by rw [hxa] at hxy; exact hxy))
    · rcases Set.mem_insert_iff.1 hy with hya | hy
      · exact hno x hx (by rw [hya] at hxy; exact hxy)
      · exact hcf x hx y hy hxy
  have heq := hmax _ hins (Set.subset_insert a S)
  exact haS (heq ▸ Set.mem_insert a S)

theorem s_stable_completeAF_iff (n : ℕ) (hn : 0 < n) (S : Set (Fin n)) :
    Stable (completeAF n) S ↔ ∃ a, S = {a} := by
  constructor
  · rintro ⟨hcf, hst⟩
    have hsub : S.Subsingleton := (s_conflictFree_completeAF_iff n S).1 hcf
    rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · obtain ⟨b, hb, -⟩ := hst ⟨0, hn⟩ (by simp)
      exact absurd hb (by simp)
    · exact ⟨a, hsub.eq_singleton_of_mem ha⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(s_conflictFree_completeAF_iff n _).2 Set.subsingleton_singleton, ?_⟩
    intro b hb
    exact ⟨a, rfl, fun h => hb h.symm⟩

theorem s_stable_completeAF_ncard (n : ℕ) (hn : 0 < n) :
    Set.ncard {S : Set (Fin n) | Stable (completeAF n) S} = n := by
  have hinj : Function.Injective (fun a : Fin n => ({a} : Set (Fin n))) := by
    intro a b h; simpa using h
  have hset : {S : Set (Fin n) | Stable (completeAF n) S}
      = Set.range (fun a : Fin n => ({a} : Set (Fin n))) := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_range, s_stable_completeAF_iff n hn S]
    exact ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, h.symm⟩⟩
  rw [hset, ← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem solution (n : ℕ) (hn : 0 < n) :
    Set.ncard {S : Set (Fin n) | Stable (completeAF n) S} = n :=
  s_stable_completeAF_ncard n hn
