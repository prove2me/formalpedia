-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_multiCopies_bridgeless
-- name    : Bridges.InfiniteCubicMatchings.multiCopies_bridgeless
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:25:13.884541+00:00
-- url     : https://prove2.me/theorems/b0f6b4f2-f4fb-4905-a85d-d048c7afd6c6
-- title:
--   Copies of a bridgeless graph are bridgeless: reachability avoiding a deleted edge is
-- statement:
--   Copies of a bridgeless graph are bridgeless: reachability avoiding a deleted edge is
--   transported along the inclusion of a single copy.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.multiCopies_bridgeless{ι : Type*} {K : SimpleGraph W} (hb : Bridgeless K) :
--       Bridgeless (multiCopies ι K) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsMSTransfer.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsMSTransfer.lean#L210

-- Thm stub generated from Bridges/InfiniteCubicMatchingsMSTransfer.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsEquivalence
import Definitions.Def_Bridges_InfiniteCubicMatchingsMSTransfer
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

theorem Bridges.InfiniteCubicMatchings.multiCopies_bridgeless{ι : Type*} {K : SimpleGraph W} (hb : Bridgeless K) :
    Bridgeless (multiCopies ι K) := by sorry
