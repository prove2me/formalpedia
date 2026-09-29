-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_exists_bfCond_of_localIso
-- name    : Bridges.InfiniteCubicMatchings.exists_bfCond_of_localIso
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:23:14.592606+00:00
-- url     : https://prove2.me/theorems/a41c0a5a-30fc-4216-8422-eebc0e27fd6f
-- title:
--   Pullback of a Berge–Fulkerson family along a local isomorphism.
-- statement:
--   **Pullback of a Berge–Fulkerson family along a local isomorphism.**  If `φ` is a local
--   isomorphism at every vertex satisfying `P`, then a Berge–Fulkerson family of the model graph
--   `K` pulls back to a configuration satisfying the local Berge–Fulkerson condition at every
--   `P`-vertex all of whose neighbours are `P`-vertices.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.exists_bfCond_of_localIso{K : SimpleGraph W} (φ : V → W)
--       (M : Fin 6 → PerfectMatching K)
--       (hM : ∀ e ∈ K.edgeSet, {i : Fin 6 | e ∈ (M i).edges}.ncard = 2)
--       (hne : ∀ v : V, (G.neighborSet v).Nonempty)
--       (P : V → Prop) (hP : ∀ v, P v → IsLocalIsoAt G K φ v) :
--       ∃ c : BFConfig G, ∀ v, P v → (∀ x, G.Adj v x → P x) → BFCond G c v := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsCompactness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsCompactness.lean#L162

-- Thm stub generated from Bridges/InfiniteCubicMatchingsCompactness.lean
import Mathlib
import Definitions.Def_Bridges_InfiniteCubicMatchings
import Definitions.Def_Bridges_InfiniteCubicMatchingsCompactness
/-
# Compactness: transferring the Berge–Fulkerson property from finite to infinite graphs

The paper *On some perfect matching conjectures in infinite, cubic, bridgeless graphs*
proves that the finite versions of the Berge–Fulkerson, Fan–Raspaud and Máčajová–Škoviera
conjectures are equivalent to their infinite versions.  The engine behind such statements is
a compactness (Rado selection / Tychonoff) argument.  This file formalises that engine.

Main results:

* `exists_forall_of_forall_finset` : a general compactness principle.  A constraint system on
  a product of *finite* sets, each constraint depending only on finitely many coordinates, is
  satisfiable as soon as every finite subsystem is.
* `bergeFulkerson_iff_locallyApproximable` : for a locally finite graph, the Berge–Fulkerson
  property is **finitary**: it holds iff every finite set of vertices carries a partial
  Berge–Fulkerson configuration.  (This is the exact local-to-global content of the transfer
  theorem.)
* `bergeFulkerson_of_finite_local_models` : if the *finite* Berge–Fulkerson conjecture holds
  and the (possibly infinite) locally finite graph `G` admits, around every finite set of
  vertices, a finite cubic bridgeless *local model*, then `G` satisfies Berge–Fulkerson.
-/

open Bridges.InfiniteCubicMatchings

universe u v w

/-! ## A general compactness principle -/


/-! ## Berge–Fulkerson configurations -/

variable {V : Type u} {G : SimpleGraph V}







/-! ## Finite local models: the finite conjecture transfers to infinite graphs -/

variable {W : Type v}

theorem Bridges.InfiniteCubicMatchings.exists_bfCond_of_localIso{K : SimpleGraph W} (φ : V → W)
    (M : Fin 6 → PerfectMatching K)
    (hM : ∀ e ∈ K.edgeSet, {i : Fin 6 | e ∈ (M i).edges}.ncard = 2)
    (hne : ∀ v : V, (G.neighborSet v).Nonempty)
    (P : V → Prop) (hP : ∀ v, P v → IsLocalIsoAt G K φ v) :
    ∃ c : BFConfig G, ∀ v, P v → (∀ x, G.Adj v x → P x) → BFCond G c v := by sorry
