-- Prove2me | solution 1 for Bridges.InfiniteCubicMatchings.macajovaSkoviera_of_injective_finite_local_models
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:07:23.288946+00:00
-- url     : https://prove2.me/submissions/e8223352-16ec-4f8f-b69f-10bfe0cf4cc5

-- Sol generated from Bridges/InfiniteCubicMatchingsMSTransfer.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Definitions.Def_Bridges_InfiniteCubicMatchingsEquivalence
import Definitions.Def_Bridges_InfiniteCubicMatchingsMSTransfer
import Theorems.Thm_Bridges_InfiniteCubicMatchings_exists_msCond_of_localIso
import Theorems.Thm_Bridges_InfiniteCubicMatchings_macajovaSkoviera_iff_locallyApproximable
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
theorem solution    (hlf : ∀ v : V, (G.neighborSet v).Finite) (hne : ∀ v : V, (G.neighborSet v).Nonempty)
    (hMS : FiniteMacajovaSkovieraConjecture) (hmod : HasInjectiveFiniteLocalModels G) :
    MacajovaSkoviera G := by
  classical
  rw [macajovaSkoviera_iff_locallyApproximable hlf]
  intro T
  set T' : Finset V :=
    T.biUnion (fun j => match j with
      | Sum.inl v => insert v (hlf v).toFinset
      | Sum.inr S => S) with hT'
  obtain ⟨W, hWfin, K, φ, hcub, hbr, hiso, hinj⟩ := hmod T'
  obtain ⟨M₁, M₂, hMcut⟩ := hMS W hWfin K hcub hbr
  obtain ⟨c, hinvol, hcut⟩ := exists_msCond_of_localIso (G := G) φ ![M₁, M₂]
    (by simpa using hMcut) hne (fun v => v ∈ T') (fun v hv => hiso v hv)
  refine ⟨c, ?_⟩
  rintro (v | S) hj
  · have hv : v ∈ T' := Finset.mem_biUnion.mpr ⟨Sum.inl v, hj, Finset.mem_insert_self _ _⟩
    refine hinvol v hv (fun y hy => ?_)
    exact Finset.mem_biUnion.mpr ⟨Sum.inl v, hj, Finset.mem_insert_of_mem (by simpa using hy)⟩
  · intro hS
    have hsub : ∀ u ∈ S, u ∈ T' := fun u hu => Finset.mem_biUnion.mpr ⟨Sum.inr S, hj, hu⟩
    refine hcut S hsub (fun a ha b hb hab => ?_) hS
    exact hinj (Finset.mem_coe.mpr (hsub a (Finset.mem_coe.mp ha)))
      (Finset.mem_coe.mpr (hsub b (Finset.mem_coe.mp hb))) hab
