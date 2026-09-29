-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_fanRaspaud_of_finite_local_models
-- name    : Bridges.InfiniteCubicMatchings.fanRaspaud_of_finite_local_models
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:24:59.977892+00:00
-- url     : https://prove2.me/theorems/b70bdbdd-0af0-4a65-a550-0ec7048ee9ef
-- title:
--   Transfer theorem for Fan–Raspaud.
-- statement:
--   **Transfer theorem for Fan–Raspaud.**  Assuming the finite Fan–Raspaud conjecture, a
--   locally finite graph without isolated vertices which has finite cubic bridgeless local models
--   around every finite vertex set satisfies Fan–Raspaud.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.fanRaspaud_of_finite_local_models    (hlf : ∀ v : V, (G.neighborSet v).Finite) (hne : ∀ v : V, (G.neighborSet v).Nonempty)
--       (hFR : FiniteFanRaspaudConjecture)
--       (hmodels : ∀ T : Finset V, ∃ (W : Type) (_ : Fintype W) (K : SimpleGraph W) (φ : V → W),
--           IsCubic K ∧ Bridgeless K ∧ ∀ v ∈ T, IsLocalIsoAt G K φ v) :
--       FanRaspaud G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsCompactness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsCompactness.lean#L420

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





/-! ## The same for Fan–Raspaud and Máčajová–Škoviera

All three properties are *finitary*: they are determined by their restrictions to finite sets
of vertices.  We set up the two remaining cases with the same machinery. -/






/-! ### Fan–Raspaud -/




/-! ### Máčajová–Škoviera -/




/-! ### Finite local models for Fan–Raspaud

The same pullback argument as for Berge–Fulkerson, one dimension lower. -/

theorem Bridges.InfiniteCubicMatchings.fanRaspaud_of_finite_local_models    (hlf : ∀ v : V, (G.neighborSet v).Finite) (hne : ∀ v : V, (G.neighborSet v).Nonempty)
    (hFR : FiniteFanRaspaudConjecture)
    (hmodels : ∀ T : Finset V, ∃ (W : Type) (_ : Fintype W) (K : SimpleGraph W) (φ : V → W),
        IsCubic K ∧ Bridgeless K ∧ ∀ v ∈ T, IsLocalIsoAt G K φ v) :
    FanRaspaud G := by sorry
