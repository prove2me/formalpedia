-- Prove2me | solution 1 for ArgTop.preferred_iff_maximalConflictFree_of_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-15T19:07:51.846851+00:00
-- url     : https://prove2.me/submissions/202c7321-8477-4f80-9944-977a2e456758

-- Thm stub generated from Novelty/ArgumentationSymmetric.lean
import Mathlib
import Definitions.Def_Novelty_ArgumentationSymmetric

/-!
# The topology of argumentation, IV: symmetric frameworks, naive extensions, and the Euler bridge

This file continues the study of the *conflict-free complex* `K(AF)` of a Dung
argumentation framework `(A, R)` begun in `ArgumentationCore`.  It isolates the
class of **symmetric** frameworks — those where attacks come in pairs
(`R a b → R b a`), the natural setting for mutual disagreement — and establishes
the precise dictionary between the *semantics* of the framework and the
*combinatorial topology* of its complex.

## Main results

* `conflictFree_admissible_of_symmetric` — in a symmetric framework every
  conflict-free set is admissible: each argument defends *itself*, because an
  attacker is always attacked back.  Hence `admissible_iff_conflictFree_of_symmetric`.
* `preferred_iff_maximalConflictFree_of_symmetric` — the **preferred extensions
  of a symmetric framework are exactly the maximal conflict-free sets**, i.e. the
  *facets* of the complex `K(AF)` (its inclusion-maximal faces).  This is the
  key identification of a *semantic* notion (preferred = maximal credulous
  position) with a *topological* one (facet of the independence complex).
* `groundedExt_eq_unattacked_of_symmetric` — the grounded (skeptical) extension
  of a symmetric framework is precisely the set of *unattacked* arguments, the
  isolated vertices of the conflict graph.

## The complete conflict graph and the Euler bridge

For the **complete conflict graph** `completeAF n` on `n` arguments (every two
distinct arguments attack each other), the complex `K(AF)` is `n` isolated
points.  We prove:

* `conflictFree_completeAF_iff` — conflict-free = subsingleton;
* `preferred_completeAF_iff` — preferred extensions are exactly the singletons;
* `preferred_completeAF_ncard` — there are exactly `n` of them;
* `euler_completeAF` — the Euler characteristic of `K(AF)` equals `n`;
* `euler_eq_preferred_completeAF` — **the Euler characteristic equals the number
  of preferred extensions** (for `n ≥ 1`).

This is the *correct* Euler/semantics bridge: the naive identity refuted in
`ArgumentationSimplicial` is replaced, on the symmetric side, by an exact match
between `χ(K(AF))` and the count of maximal independent sets.  The hypothesis
`n ≥ 1` is sharp — see the boundary remark `euler_ne_preferred_completeAF_zero`.
-/

open ArgTop

open Finset

variable {A : Type*} {R : A → A → Prop}

/-! ## Basic Dung semantics (self-contained)

We re-declare the core notions of the conflict-free complex so that this file
compiles independently. -/







/-! ## Symmetric frameworks: conflict-free = admissible -/




/-! ## Preferred extensions and grounded extension of a symmetric framework -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

theorem t_charF_empty (R : A → A → Prop) : charF R (∅ : Set A) = {a | ∀ b, ¬ R b a} := by
  ext a; simp [charF, Defends]

theorem t_charF_groundedExt (R : A → A → Prop) : charF R (groundedExt R) = groundedExt R :=
  OrderHom.map_lfp (charFHom R)

theorem t_completeAF_symmetric (n : ℕ) : Symmetric (completeAF n) := fun _ _ h => Ne.symm h

theorem t_conflictFree_admissible_of_symmetric (hsym : Symmetric R) {S : Set A}
    (hS : ConflictFree R S) : Admissible R S :=
  ⟨hS, fun a ha b hb => ⟨a, ha, hsym hb⟩⟩

theorem t_preferred_iff_maximalConflictFree_of_symmetric (hsym : Symmetric R) {S : Set A} :
    Preferred R S ↔ MaximalConflictFree R S := by
  constructor
  · rintro ⟨⟨hcf, -⟩, hmax⟩
    exact ⟨hcf, fun T hT hST => hmax T (t_conflictFree_admissible_of_symmetric hsym hT) hST⟩
  · rintro ⟨hcf, hmax⟩
    exact ⟨t_conflictFree_admissible_of_symmetric hsym hcf, fun T hT hST => hmax T hT.1 hST⟩

theorem t_groundedExt_eq_unattacked_of_symmetric (hsym : Symmetric R) :
    groundedExt R = {a | ∀ b, ¬ R b a} := by
  apply subset_antisymm
  · refine OrderHom.lfp_le _ ?_
    intro a ha b hb
    obtain ⟨c, hc, hcb⟩ := ha b hb
    exact hc b (hsym hcb)
  · refine OrderHom.le_lfp _ ?_
    intro S hS a ha
    exact hS (fun b hb => absurd hb (ha b))

theorem t_conflictFree_completeAF_iff (n : ℕ) (S : Set (Fin n)) :
    ConflictFree (completeAF n) S ↔ S.Subsingleton := by
  constructor
  · intro h a ha b hb
    by_contra hne
    exact h a ha b hb hne
  · intro h a ha b hb hab
    exact hab (h ha hb)

theorem t_preferred_completeAF_iff (n : ℕ) (hn : 0 < n) (S : Set (Fin n)) :
    Preferred (completeAF n) S ↔ ∃ a, S = {a} := by
  rw [t_preferred_iff_maximalConflictFree_of_symmetric (t_completeAF_symmetric n)]
  constructor
  · rintro ⟨hcf, hmax⟩
    have hsub : S.Subsingleton := (t_conflictFree_completeAF_iff n S).1 hcf
    rcases S.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
    · exact absurd (hmax {⟨0, hn⟩}
        ((t_conflictFree_completeAF_iff n _).2 Set.subsingleton_singleton)
        (Set.empty_subset _)) (Set.singleton_ne_empty _)
    · exact ⟨a, hsub.eq_singleton_of_mem ha⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(t_conflictFree_completeAF_iff n _).2 Set.subsingleton_singleton, ?_⟩
    intro T hT hsub
    exact ((t_conflictFree_completeAF_iff n T).1 hT).eq_singleton_of_mem (hsub rfl)

theorem t_preferred_completeAF_ncard (n : ℕ) (hn : 0 < n) :
    Set.ncard {S : Set (Fin n) | Preferred (completeAF n) S} = n := by
  have hinj : Function.Injective (fun a : Fin n => ({a} : Set (Fin n))) := by
    intro a b h; simpa using h
  have hset : {S : Set (Fin n) | Preferred (completeAF n) S}
      = Set.range (fun a : Fin n => ({a} : Set (Fin n))) := by
    ext S
    simp only [Set.mem_setOf_eq, Set.mem_range, t_preferred_completeAF_iff n hn S]
    exact ⟨fun ⟨a, h⟩ => ⟨a, h.symm⟩, fun ⟨a, h⟩ => ⟨a, h.symm⟩⟩
  rw [hset, ← Set.image_univ, Set.ncard_image_of_injective _ hinj, Set.ncard_univ,
    Nat.card_eq_fintype_card, Fintype.card_fin]

theorem t_euler_completeAF (n : ℕ) : eulerChar (facesFinset (completeAF n)) = n := by
  classical
  have hF : facesFinset (completeAF n)
      = insert (∅ : Finset (Fin n))
        (Finset.univ.image (fun a : Fin n => ({a} : Finset (Fin n)))) := by
    ext s
    simp only [facesFinset, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_image]
    constructor
    · intro h
      have hsub : (↑s : Set (Fin n)).Subsingleton := (t_conflictFree_completeAF_iff n _).1 h
      rcases Finset.eq_empty_or_nonempty s with rfl | ⟨a, ha⟩
      · exact Or.inl rfl
      · refine Or.inr ⟨a, ?_⟩
        refine Finset.Subset.antisymm ?_ ?_
        · intro b hb
          have hba : b = a := Finset.mem_singleton.1 hb
          subst hba
          exact ha
        · intro b hb
          exact Finset.mem_singleton.2 (hsub (by simpa using hb) (by simpa using ha))
    · rintro (rfl | ⟨a, rfl⟩)
      · exact (t_conflictFree_completeAF_iff n _).2 (by simp)
      · exact (t_conflictFree_completeAF_iff n _).2 (by simp)
  rw [hF, eulerChar, Finset.sum_insert (by simp), Finset.sum_image (by
    intro a _ b _ h; simpa using h)]
  simp

theorem solution (hsym : Symmetric R) {S : Set A} :
    Preferred R S ↔ MaximalConflictFree R S :=
  t_preferred_iff_maximalConflictFree_of_symmetric hsym
