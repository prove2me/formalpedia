-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_macajovaSkoviera_iff_locallyApproximable
-- name    : Bridges.InfiniteCubicMatchings.macajovaSkoviera_iff_locallyApproximable
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:28:41.222795+00:00
-- url     : https://prove2.me/theorems/c9cd8258-2944-409b-8660-429c42968679
-- title:
--   Local-to-global theorem for Máčajová–Škoviera.
-- statement:
--   **Local-to-global theorem for Máčajová–Škoviera.**
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.macajovaSkoviera_iff_locallyApproximable(hlf : ∀ v : V, (G.neighborSet v).Finite) :
--       MacajovaSkoviera G ↔ MSLocallyApproximable G := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsCompactness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsCompactness.lean#L336

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

theorem Bridges.InfiniteCubicMatchings.macajovaSkoviera_iff_locallyApproximable(hlf : ∀ v : V, (G.neighborSet v).Finite) :
    MacajovaSkoviera G ↔ MSLocallyApproximable G := by sorry
