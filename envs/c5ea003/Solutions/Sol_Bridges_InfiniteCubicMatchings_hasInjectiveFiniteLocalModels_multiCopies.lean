-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.hasInjectiveFiniteLocalModels_multiCopies
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:48:35.232915+00:00
-- url     : https://prove2.me/submissions/2f172d4c-a5b7-4801-a208-3f640a6c2a60

-- Sol generated from Bridges/InfiniteCubicMatchingsMSTransfer.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Definitions.Def_Bridges_InfiniteCubicMatchingsEquivalence
import Definitions.Def_Bridges_InfiniteCubicMatchingsMSTransfer
import Theorems.Thm_Bridges_InfiniteCubicMatchings_multiCopies_bridgeless
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


@[simp] lemma multiCopies_adj {ι : Type*} {K : SimpleGraph W} (p q : ι × W) :
    (multiCopies ι K).Adj p q ↔ p.1 = q.1 ∧ K.Adj p.2 q.2 := Iff.rfl

lemma multiCopies_neighborSet {ι : Type*} {K : SimpleGraph W} (i : ι) (a : W) :
    (multiCopies ι K).neighborSet (i, a) = (fun b => (i, b)) '' K.neighborSet a := by
  ext ⟨j, b⟩
  simp only [SimpleGraph.mem_neighborSet, multiCopies_adj, Set.mem_image, Prod.mk.injEq]
  constructor
  · rintro ⟨rfl, h⟩
    exact ⟨b, h, rfl, rfl⟩
  · rintro ⟨b', hb', rfl, rfl⟩
    exact ⟨rfl, hb'⟩

theorem multiCopies_isCubic {ι : Type*} {K : SimpleGraph W} (hc : IsCubic K) :
    IsCubic (multiCopies ι K) := by
  rintro ⟨i, a⟩
  rw [multiCopies_neighborSet,
    Set.ncard_image_of_injective _ (fun b b' h => congrArg Prod.snd h)]
  exact hc a





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
theorem solution{W : Type} {K : SimpleGraph W} [Fintype W]
    (hc : IsCubic K) (hb : Bridgeless K) :
    HasInjectiveFiniteLocalModels (multiCopies ℕ K) := by
  classical
  intro T
  set N : ℕ := T.sup Prod.fst with hN
  refine ⟨Fin (N + 1) × W, inferInstance, multiCopies (Fin (N + 1)) K,
    fun p => (⟨min p.1 N, by omega⟩, p.2), multiCopies_isCubic hc, multiCopies_bridgeless hb,
    ?_, ?_⟩
  · rintro ⟨m, a⟩ -
    refine ⟨?_, ?_, ?_⟩
    · rintro ⟨m', a'⟩ ⟨hm, ha⟩
      simp only at hm ha
      subst hm
      exact ⟨rfl, ha⟩
    · rintro ⟨m₁, a₁⟩ ⟨m₂, a₂⟩ ⟨hm₁, ha₁⟩ ⟨hm₂, ha₂⟩ hEq
      simp only at hm₁ hm₂
      subst hm₁; subst hm₂
      have h2 : a₁ = a₂ := by simpa using congrArg Prod.snd hEq
      rw [h2]
    · rintro ⟨k, b⟩ ⟨hk, hab⟩
      simp only at hk hab
      exact ⟨(m, b), ⟨rfl, hab⟩, by rw [Prod.ext_iff]; exact ⟨hk.symm ▸ rfl, rfl⟩⟩
  · rintro ⟨m₁, a₁⟩ h₁ ⟨m₂, a₂⟩ h₂ hEq
    have hb₁ : m₁ ≤ N := Finset.le_sup (f := Prod.fst) (Finset.mem_coe.mp h₁)
    have hb₂ : m₂ ≤ N := Finset.le_sup (f := Prod.fst) (Finset.mem_coe.mp h₂)
    have h1 : min m₁ N = min m₂ N := congrArg Fin.val (congrArg Prod.fst hEq)
    have h2 : a₁ = a₂ := congrArg Prod.snd hEq
    rw [min_eq_left hb₁, min_eq_left hb₂] at h1
    exact Prod.ext h1 h2
