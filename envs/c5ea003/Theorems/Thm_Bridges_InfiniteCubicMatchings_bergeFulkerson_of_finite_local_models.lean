-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_bergeFulkerson_of_finite_local_models
-- name    : Bridges.InfiniteCubicMatchings.bergeFulkerson_of_finite_local_models
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:23:22.330404+00:00
-- url     : https://prove2.me/theorems/0855f9a8-72c6-45b0-b19a-1a742bba0a6b
-- title:
--   Transfer theorem.
-- statement:
--   **Transfer theorem.**  Assume the finite Berge–Fulkerson conjecture.  If a locally finite
--   graph `G` with no isolated vertices admits, around every finite set of vertices, a *finite
--   cubic bridgeless local model*, then `G` itself satisfies the Berge–Fulkerson property.
--
--   This is the compactness half of the equivalence "finite version ⟺ infinite version": the
--   combinatorial input that remains is the construction of the finite local models.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.bergeFulkerson_of_finite_local_models    (hlf : ∀ v : V, (G.neighborSet v).Finite) (hne : ∀ v : V, (G.neighborSet v).Nonempty)
--       (hBF : FiniteBergeFulkersonConjecture)
--       (hmodels : ∀ T : Finset V, ∃ (W : Type) (_ : Fintype W) (K : SimpleGraph W) (φ : V → W),
--           IsCubic K ∧ Bridgeless K ∧ ∀ v ∈ T, IsLocalIsoAt G K φ v) :
--       BergeFulkerson G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsCompactness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsCompactness.lean#L209

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

theorem Bridges.InfiniteCubicMatchings.bergeFulkerson_of_finite_local_models    (hlf : ∀ v : V, (G.neighborSet v).Finite) (hne : ∀ v : V, (G.neighborSet v).Nonempty)
    (hBF : FiniteBergeFulkersonConjecture)
    (hmodels : ∀ T : Finset V, ∃ (W : Type) (_ : Fintype W) (K : SimpleGraph W) (φ : V → W),
        IsCubic K ∧ Bridgeless K ∧ ∀ v ∈ T, IsLocalIsoAt G K φ v) :
    BergeFulkerson G := by sorry
