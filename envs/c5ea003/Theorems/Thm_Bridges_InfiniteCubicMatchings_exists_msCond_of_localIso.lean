-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_exists_msCond_of_localIso
-- name    : Bridges.InfiniteCubicMatchings.exists_msCond_of_localIso
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:24:31.791622+00:00
-- url     : https://prove2.me/theorems/a7c98dab-bcc0-4913-9488-f38c7c96ff96
-- title:
--   Pullback of a Máčajová–Škoviera pair along a local isomorphism.
-- statement:
--   **Pullback of a Máčajová–Škoviera pair along a local isomorphism.**  If `φ` is a local
--   isomorphism at every `P`-vertex and `M 0, M 1` is a Máčajová–Škoviera pair of the model `K`,
--   then the pulled-back configuration is involutive at every `P`-vertex whose neighbours are
--   `P`-vertices, and refutes the odd-cut condition for every odd `P`-window on which `φ` is
--   injective.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.exists_msCond_of_localIso{K : SimpleGraph W} (φ : V → W) (M : Fin 2 → PerfectMatching K)
--       (hM : ∀ C, IsOddCut K C → ¬ C ⊆ (M 0).edges ∩ (M 1).edges)
--       (hne : ∀ v : V, (G.neighborSet v).Nonempty)
--       (P : V → Prop) (hP : ∀ v, P v → IsLocalIsoAt G K φ v) :
--       ∃ c : MConfig G 2,
--         (∀ v, P v → (∀ x, G.Adj v x → P x) → InvolCond G c v) ∧
--         (∀ S : Finset V, (∀ u ∈ S, P u) → Set.InjOn φ ↑S → Odd S.card →
--           ∃ u ∈ S, ∃ w, G.Adj u w ∧ w ∉ S ∧ ¬ ((c u 0 : V) = w ∧ (c u 1 : V) = w)) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsMSTransfer.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsMSTransfer.lean#L66

-- Thm stub generated from Bridges/InfiniteCubicMatchingsMSTransfer.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsBridged
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
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

theorem Bridges.InfiniteCubicMatchings.exists_msCond_of_localIso{K : SimpleGraph W} (φ : V → W) (M : Fin 2 → PerfectMatching K)
    (hM : ∀ C, IsOddCut K C → ¬ C ⊆ (M 0).edges ∩ (M 1).edges)
    (hne : ∀ v : V, (G.neighborSet v).Nonempty)
    (P : V → Prop) (hP : ∀ v, P v → IsLocalIsoAt G K φ v) :
    ∃ c : MConfig G 2,
      (∀ v, P v → (∀ x, G.Adj v x → P x) → InvolCond G c v) ∧
      (∀ S : Finset V, (∀ u ∈ S, P u) → Set.InjOn φ ↑S → Odd S.card →
        ∃ u ∈ S, ∃ w, G.Adj u w ∧ w ∉ S ∧ ¬ ((c u 0 : V) = w ∧ (c u 1 : V) = w)) := by sorry
