-- Prove2me | Theorems.Thm_Bridges_InfiniteCubicMatchings_exists_forall_of_forall_finset
-- name    : Bridges.InfiniteCubicMatchings.exists_forall_of_forall_finset
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:22:54.988782+00:00
-- url     : https://prove2.me/theorems/c68639e7-5605-4bdd-bab9-90de6df786a6
-- title:
--   Compactness principle.
-- statement:
--   **Compactness principle.**  Let `K i` be finite sets and consider constraints `P j` on
--   the product `∀ i, K i`, each `P j` depending only on the coordinates in some finite set
--   `D j`.  If every finite subsystem of the constraints is satisfiable, the whole system is.
--
--   ```lean
--   theorem Bridges.InfiniteCubicMatchings.exists_forall_of_forall_finset{ι : Type u} {K : ι → Type v} [∀ i, Finite (K i)]
--       {J : Type w} (P : J → (∀ i, K i) → Prop)
--       (hloc : ∀ j, ∃ D : Finset ι, ∀ c d : (∀ i, K i), (∀ i ∈ D, c i = d i) → P j c → P j d)
--       (hfin : ∀ T : Finset J, ∃ c, ∀ j ∈ T, P j c) :
--       ∃ c, ∀ j, P j c := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/InfiniteCubicMatchingsCompactness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/InfiniteCubicMatchingsCompactness.lean#L29

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

theorem Bridges.InfiniteCubicMatchings.exists_forall_of_forall_finset{ι : Type u} {K : ι → Type v} [∀ i, Finite (K i)]
    {J : Type w} (P : J → (∀ i, K i) → Prop)
    (hloc : ∀ j, ∃ D : Finset ι, ∀ c d : (∀ i, K i), (∀ i ∈ D, c i = d i) → P j c → P j d)
    (hfin : ∀ T : Finset J, ∃ c, ∀ j ∈ T, P j c) :
    ∃ c, ∀ j, P j c := by sorry
