-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.exists_msCond_of_localIso
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:42:37.457575+00:00
-- url     : https://prove2.me/submissions/c5258b23-cb06-4fb9-893e-b58cfc31002b

-- Sol generated from Bridges/InfiniteCubicMatchingsMSTransfer.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Definitions.Def_Bridges_InfiniteCubicMatchingsEquivalence
import Definitions.Def_Bridges_InfiniteCubicMatchingsMSTransfer
import Theorems.Thm_Bridges_InfiniteCubicMatchings_PerfectMatching_mem_edges
/-
# The Máčajová–Škoviera transfer: finite ⟺ infinite

`InfiniteCubicMatchingsCompactness.lean` proves that the Berge–Fulkerson and the Fan–Raspaud
conjectures transfer from finite graphs to locally finite infinite graphs admitting *finite
local models*, and `InfiniteCubicMatchingsEquivalence.lean` turns those transfers into
equivalences.  The Máčajová–Škoviera conjecture was left out, because its defining condition
quantifies over **odd cuts**, i.e. over finite vertex sets, and a local isomorphism
`φ : V → W` onto a finite model need not preserve the *cardinality* of such a set: `φ` can
collapse an odd set to an even one, destroying the parity that the conjecture is about.
(This was Conjecture 4 of `FUTURE_DIRECTIONS.md`.)

This file closes that gap.  Only one extra requirement is needed: the local model must be
*faithful* on the finite window, i.e. `φ` must be injective there.  Then the image of an odd
vertex set is again odd, and the odd-cut condition pulls back.

Main results:

* `exists_msCond_of_localIso` : pullback of a Máčajová–Škoviera pair along a local
  isomorphism, including the odd-cut half of the condition on every window on which the
  local isomorphism is injective;
* `macajovaSkoviera_of_injective_finite_local_models` : the finite Máčajová–Škoviera
  conjecture implies the infinite one on the class `HasInjectiveFiniteLocalModels`;
* `finiteMacajovaSkoviera_iff` : the two conjectures are *equivalent* on that class;
* `multiCopies` and `hasInjectiveFiniteLocalModels_multiCopies` : the class is not a
  disguised finiteness assumption — the infinite graph `multiCopies ℕ K` (infinitely many
  disjoint copies of a finite cubic bridgeless graph `K`) is cubic, bridgeless, has an
  infinite vertex set, and belongs to it.
-/

open Bridges.InfiniteCubicMatchings

universe u v

variable {V : Type u} {W : Type v} {G : SimpleGraph V}

/-! ## Faithful finite local models -/





/-! ## Pullback of a Máčajová–Škoviera pair -/


/-! ## The transfer theorem and the equivalence -/




/-! ## The faithful class contains genuinely infinite graphs

A map injective on *every* finite set is injective, so a graph with infinitely many vertices
lying in `HasInjectiveFiniteLocalModels` must use larger and larger models.  Infinitely many
disjoint copies of a fixed finite cubic bridgeless graph is the simplest such example. -/









/-! ### All three properties pass unconditionally to infinite disjoint unions

Berge–Fulkerson and Fan–Raspaud transfer because the projection onto the second coordinate is
a covering map.  Máčajová–Škoviera does *not* follow from covering — the image of an odd cut
need not be odd — and is proved below by a fibre-parity argument: an odd vertex set of the
disjoint union has an odd fibre, which is an odd cut of a single copy. -/








/-! ## A concrete infinite member of the faithful class

`K₄` is finite, cubic and bridgeless, so infinitely many disjoint copies of it form an
infinite cubic bridgeless graph in `HasInjectiveFiniteLocalModels` — and all three properties
hold for it *unconditionally*. -/





open Bridges.InfiniteCubicMatchings in
theorem solution{K : SimpleGraph W} (φ : V → W) (M : Fin 2 → PerfectMatching K)
    (hM : ∀ C, IsOddCut K C → ¬ C ⊆ (M 0).edges ∩ (M 1).edges)
    (hne : ∀ v : V, (G.neighborSet v).Nonempty)
    (P : V → Prop) (hP : ∀ v, P v → IsLocalIsoAt G K φ v) :
    ∃ c : MConfig G 2,
      (∀ v, P v → (∀ x, G.Adj v x → P x) → InvolCond G c v) ∧
      (∀ S : Finset V, (∀ u ∈ S, P u) → Set.InjOn φ ↑S → Odd S.card →
        ∃ u ∈ S, ∃ w, G.Adj u w ∧ w ∉ S ∧ ¬ ((c u 0 : V) = w ∧ (c u 1 : V) = w)) := by
  classical
  have key : ∀ v : V, ∀ i : Fin 2, ∃ x : V, G.Adj v x ∧ (P v → φ x = (M i).partner (φ v)) := by
    intro v i
    by_cases h : P v
    · obtain ⟨x, hx, hxe⟩ := (hP v h).surj ((M i).partner (φ v)) ((M i).isAdj (φ v))
      exact ⟨x, hx, fun _ => hxe⟩
    · obtain ⟨x, hx⟩ := hne v
      exact ⟨x, hx, fun h' => absurd h' h⟩
  choose x hadj hphi using key
  refine ⟨fun v i => ⟨x v i, hadj v i⟩, ?_, ?_⟩
  · intro v hv hvn i
    have h1 : φ (x v i) = (M i).partner (φ v) := hphi v i hv
    have hPw : P (x v i) := hvn _ (hadj v i)
    have h2 : φ (x (x v i) i) = (M i).partner (φ (x v i)) := hphi _ i hPw
    rw [h1, (M i).invol] at h2
    exact (hP _ hPw).inj _ _ (hadj (x v i) i) (hadj v i).symm h2
  · intro S hSP hinj hodd
    have hcard : (S.image φ).card = S.card := Finset.card_image_of_injOn hinj
    have hodd' : Odd (S.image φ).card := by rw [hcard]; exact hodd
    have hnot := hM (cutEdges K (S.image φ)) ⟨S.image φ, hodd', rfl⟩
    rw [Set.not_subset] at hnot
    obtain ⟨e, heC, heM⟩ := hnot
    obtain ⟨hEe, a, b, rfl, haS, hbS⟩ := heC
    obtain ⟨u, huS, rfl⟩ := Finset.mem_image.mp haS
    have hPu : P u := hSP u huS
    obtain ⟨w, hwadj, hwb⟩ := (hP u hPu).surj b (by simpa using hEe)
    subst hwb
    refine ⟨u, huS, w, hwadj, ?_, ?_⟩
    · intro hwS
      exact hbS (Finset.mem_image_of_mem φ hwS)
    · rintro ⟨h0, h1⟩
      refine heM ⟨?_, ?_⟩ <;> rw [PerfectMatching.mem_edges]
      · rw [← hphi u 0 hPu]; exact congrArg φ h0
      · rw [← hphi u 1 hPu]; exact congrArg φ h1
