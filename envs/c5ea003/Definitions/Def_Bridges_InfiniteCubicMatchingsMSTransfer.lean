-- Prove2me | Definitions.Def_Bridges_InfiniteCubicMatchingsMSTransfer
-- name    : Bridges_InfiniteCubicMatchingsMSTransfer
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:27.255301+00:00
-- url     : https://prove2.me/theorems/7eb9e001-c96c-4aa1-b8f1-ab9b8fbbdbb7
-- title:
--   Aether Catalog definitions — Bridges_InfiniteCubicMatchingsMSTransfer
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InfiniteCubicMatchingsMSTransfer`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InfiniteCubicMatchingsMSTransfer.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
import Definitions.Def_Bridges_InfiniteCubicMatchingsEquivalence
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

namespace Bridges.InfiniteCubicMatchings

universe u v

variable {V : Type u} {W : Type v} {G : SimpleGraph V}

/-! ## Faithful finite local models -/

/-- The Máčajová–Škoviera conjecture for *finite* cubic bridgeless graphs. -/
def FiniteMacajovaSkovieraConjecture : Prop :=
  ∀ (W : Type) (_ : Fintype W) (K : SimpleGraph W), IsCubic K → Bridgeless K →
    MacajovaSkoviera K

/-- `G` *has injective (faithful) finite local models* if around every finite set `T` of
vertices it is locally isomorphic to a finite cubic bridgeless graph **by a map that is
injective on `T`**.  Injectivity is what makes odd vertex sets stay odd in the model, and it
is exactly what the Máčajová–Škoviera transfer needs on top of `HasFiniteLocalModels`. -/
def HasInjectiveFiniteLocalModels (G : SimpleGraph V) : Prop :=
  ∀ T : Finset V, ∃ (W : Type) (_ : Fintype W) (K : SimpleGraph W) (φ : V → W),
    IsCubic K ∧ Bridgeless K ∧ (∀ v ∈ T, IsLocalIsoAt G K φ v) ∧ Set.InjOn φ ↑T



/-! ## Pullback of a Máčajová–Škoviera pair -/


/-! ## The transfer theorem and the equivalence -/




/-! ## The faithful class contains genuinely infinite graphs

A map injective on *every* finite set is injective, so a graph with infinitely many vertices
lying in `HasInjectiveFiniteLocalModels` must use larger and larger models.  Infinitely many
disjoint copies of a fixed finite cubic bridgeless graph is the simplest such example. -/

/-- `multiCopies ι K` is the disjoint union of `ι` copies of `K`. -/
def multiCopies (ι : Type*) (K : SimpleGraph W) : SimpleGraph (ι × W) where
  Adj p q := p.1 = q.1 ∧ K.Adj p.2 q.2
  symm := by
    rintro p q ⟨h1, h2⟩
    exact ⟨h1.symm, h2.symm⟩
  loopless := ⟨fun _ h => K.irrefl h.2⟩








/-! ### All three properties pass unconditionally to infinite disjoint unions

Berge–Fulkerson and Fan–Raspaud transfer because the projection onto the second coordinate is
a covering map.  Máčajová–Škoviera does *not* follow from covering — the image of an odd cut
need not be odd — and is proved below by a fibre-parity argument: an odd vertex set of the
disjoint union has an odd fibre, which is an odd cut of a single copy. -/





/-- A perfect matching of `K` acting copywise is a perfect matching of `multiCopies ι K`. -/
def PerfectMatching.multiCopiesLift {ι : Type*} {K : SimpleGraph W} (M : PerfectMatching K) :
    PerfectMatching (multiCopies ι K) where
  partner p := (p.1, M.partner p.2)
  isAdj p := ⟨rfl, M.isAdj p.2⟩
  invol p := by simp [M.invol]



/-! ## A concrete infinite member of the faithful class

`K₄` is finite, cubic and bridgeless, so infinitely many disjoint copies of it form an
infinite cubic bridgeless graph in `HasInjectiveFiniteLocalModels` — and all three properties
hold for it *unconditionally*. -/




end Bridges.InfiniteCubicMatchings


