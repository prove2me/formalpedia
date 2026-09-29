-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_macajovaSkoviera_of_injective_finite_local_models
-- name    : Bridges.InfiniteCubicMatchings.macajovaSkoviera_of_injective_finite_local_models
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:28:27.269117+00:00
-- url     : https://prove2.me/theorems/22ddb69b-8d82-4613-8ceb-f83280136680
-- title:
--   Transfer theorem for Máčajová–Škoviera.
-- statement:
--   **Transfer theorem for Máčajová–Škoviera.**  Assuming the finite Máčajová–Škoviera
--   conjecture, every locally finite graph without isolated vertices that admits *faithful*
--   finite cubic bridgeless local models satisfies the Máčajová–Škoviera property.
--
--   This is the analogue for `MacajovaSkoviera` of `bergeFulkerson_of_finite_local_models` and
--   `fanRaspaud_of_finite_local_models`; the extra injectivity of the modelling map is what
--   transports the parity of an odd cut into the finite model.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.macajovaSkoviera_of_injective_finite_local_models    (hlf : ∀ v : V, (G.neighborSet v).Finite) (hne : ∀ v : V, (G.neighborSet v).Nonempty)
--       (hMS : FiniteMacajovaSkovieraConjecture) (hmod : HasInjectiveFiniteLocalModels G) :
--       MacajovaSkoviera G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsMSTransfer.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsMSTransfer.lean#L116

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

theorem Bridges.InfiniteCubicMatchings.macajovaSkoviera_of_injective_finite_local_models    (hlf : ∀ v : V, (G.neighborSet v).Finite) (hne : ∀ v : V, (G.neighborSet v).Nonempty)
    (hMS : FiniteMacajovaSkovieraConjecture) (hmod : HasInjectiveFiniteLocalModels G) :
    MacajovaSkoviera G := by sorry
