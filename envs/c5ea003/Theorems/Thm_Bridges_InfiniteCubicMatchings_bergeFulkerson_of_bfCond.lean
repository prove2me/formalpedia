-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_bergeFulkerson_of_bfCond
-- name    : Bridges.InfiniteCubicMatchings.bergeFulkerson_of_bfCond
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:23:02.831633+00:00
-- url     : https://prove2.me/theorems/9603db1d-9108-486d-9313-9797c1ccc2ad
-- title:
--   A configuration satisfying the Berge–Fulkerson condition everywhere yields six perfect
-- statement:
--   A configuration satisfying the Berge–Fulkerson condition everywhere yields six perfect
--   matchings covering every edge twice.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.bergeFulkerson_of_bfCond(c : BFConfig G) (hc : ∀ v, BFCond G c v) :
--       BergeFulkerson G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsCompactness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsCompactness.lean#L86

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

theorem Bridges.InfiniteCubicMatchings.bergeFulkerson_of_bfCond(c : BFConfig G) (hc : ∀ v, BFCond G c v) :
    BergeFulkerson G := by sorry
