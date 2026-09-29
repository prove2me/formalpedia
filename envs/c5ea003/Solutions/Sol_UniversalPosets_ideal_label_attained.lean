-- Prove2me | solution 1 for UniversalPosets.ideal_label_attained
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:28:41.52384+00:00
-- url     : https://prove2.me/submissions/9d9f86cf-09cd-4bb9-8369-a362c359d707

-- Sol generated from Cryptography/UniversalPosets/IdealHost.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_IdealHost
import Definitions.Def_Cryptography_UniversalPosets_MinSize

/-!
# The host of nonempty ideals: `U(n) ≤ 2^n - 1`

`Bounds.lean` uses the full Boolean lattice `Set (Fin n)` as a universal host,
of size `2^n`.  This file records the (small but strict) improvement obtained by
noticing that the labelling used there — `x ↦ {y | y ≤ x}`, the *principal
ideal* of `x` — never produces the empty label, because `x` always belongs to
its own ideal.  Deleting the empty set from the Boolean lattice therefore leaves
a universal host:

`minUniversalSize n ≤ 2 ^ n - 1`.

The host is the poset of **nonempty** subsets of an `n`-element set ordered by
inclusion; the embedding is again by principal ideals, and it is *induced*
because `x ≤ y ↔ ideal x ⊆ ideal y` in any partial order.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer).  Every label used by the Boolean-lattice embedding
contains the element it labels, so the empty label is never used; more
generally, the label of `x` determines `x` as its own maximum along any linear
extension, so the labels are exactly the nonempty subsets, and no further
subset can be deleted from this particular *scheme*.

Experiment (Experimenter).  The deletion of `∅` is formalised below.  Attempts
to delete a second subset fail for this scheme: for every nonempty `S ⊆ [n]`
and every `x ∈ S` there is a poset (make `S \ {x}` an antichain below `x`, all
other points isolated) whose ideal labelling uses exactly the label `S`; this is
`ideal_label_attained`.

Analysis (Analyst).  The improvement is by one point, not by an exponential
factor: the ideal scheme is intrinsically `2^n`-sized, and beating it requires
the fundamentally different, regularity-based labelling of the motivating paper.
What the file does establish is that the naive bound `2^n` is *never* attained,
so the sandwich `2^{n/4} ≤ U(n) < 2^n` is strict at the top for every `n ≥ 1`.

Critique (Critic).  Nothing is vacuous: the host is an explicit finite poset
whose cardinality is computed, the embedding is exhibited, and the accompanying
`ideal_label_attained` shows the bound is optimal *for this labelling scheme*
(it does not claim optimality of `U`).
-/

open UniversalPosets

open Function

variable {n : ℕ}


instance : Fintype (NeHost n) := inferInstanceAs (Fintype {S : Finset (Fin n) // S.Nonempty})


@[simp] theorem NeHost.le_def (S T : NeHost n) : S ≤ T ↔ S.1 ⊆ T.1 := Iff.rfl






open UniversalPosets in
theorem solution{n : ℕ} (S : Set (Fin n)) (x : Fin n) (hx : x ∈ S) :
    ∃ r : Fin n → Fin n → Prop, IsPartialOrder (Fin n) r ∧ {y | r y x} = S := by
  classical
  refine ⟨fun a b => a = b ∨ (a ∈ S ∧ b = x ∧ a ≠ x), ?_, ?_⟩
  · refine
      haveI : Std.Refl (fun a b : Fin n => a = b ∨ (a ∈ S ∧ b = x ∧ a ≠ x)) :=
        ⟨fun _ => Or.inl rfl⟩
      haveI : IsTrans (Fin n) (fun a b : Fin n => a = b ∨ (a ∈ S ∧ b = x ∧ a ≠ x)) := ?_
      haveI : IsPreorder (Fin n) (fun a b : Fin n => a = b ∨ (a ∈ S ∧ b = x ∧ a ≠ x)) := ⟨⟩
      haveI : Std.Antisymm (fun a b : Fin n => a = b ∨ (a ∈ S ∧ b = x ∧ a ≠ x)) := ?_
      ⟨⟩
    · refine ⟨?_⟩
      rintro a b c (rfl | ⟨ha, rfl, hax⟩) (h2 | ⟨hb, rfl, hbx⟩)
      · exact Or.inl h2
      · exact Or.inr ⟨hb, rfl, hbx⟩
      · exact Or.inr ⟨ha, h2 ▸ rfl, hax⟩
      · exact absurd rfl hbx
    · refine ⟨?_⟩
      rintro a b (rfl | ⟨ha, rfl, hax⟩) (h2 | ⟨hb, rfl, hbx⟩)
      · rfl
      · exact absurd rfl hbx
      · exact h2.symm
      · exact absurd rfl hax
  · ext y
    by_cases hy : y = x
    · subst hy; simp [hx]
    · simp [hy, Set.mem_setOf_eq]
