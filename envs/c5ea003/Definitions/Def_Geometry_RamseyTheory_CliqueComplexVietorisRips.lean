-- Prove2me | Definitions.Def_Geometry_RamseyTheory_CliqueComplexVietorisRips
-- name    : Geometry_RamseyTheory_CliqueComplexVietorisRips
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:52:45.479831+00:00
-- url     : https://prove2.me/theorems/03f029ae-146b-40bf-953c-423012d46524
-- title:
--   Aether Catalog definitions — Geometry_RamseyTheory_CliqueComplexVietorisRips
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.RamseyTheory.CliqueComplexVietorisRips`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/RamseyTheory/CliqueComplexVietorisRips.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_RamseyTheory_CliqueComplexFlag
/-
# Extremes of the Vietoris–Rips Filtration, and Complement Duality

Building on `Catalog/Geometry/CliqueComplexFlag.lean`, this file pins down the two
*extremes* of the Vietoris–Rips filtration `ε ↦ vietorisRips d ε` and records the
self-duality of the clique construction under graph complementation.

## Main results

* `vietorisRips_full_of_bounded`      — above the diameter, the VR complex is the
                                         full simplex (every finite set is a face).
* `vietorisRips_discrete_of_separated`— below the minimum separation, the VR complex
                                         is discrete (faces are exactly the `≤ 1`-sets).
* `independenceComplex`               — the independence complex of a graph.
* `mem_independenceComplex`           — `independenceComplex G = cliqueComplex Gᶜ`.
* `independenceComplex_isFlag`        — flagness transfers to independence complexes.

-- !-- Lab Notebook -- !--
Hypothesis: the qualitative shape of the VR filtration is fixed by two thresholds
  (diameter above, minimum separation below), and the clique construction is
  self-dual under complementation.
Result: proved both extremes (full simplex above the diameter, discrete below the
  separation) and the complement-duality `independenceComplex G = cliqueComplex Gᶜ`,
  from which flagness is inherited for free.
Insight: face membership in `vietorisRips d ε` is a finite conjunction of scalar
  inequalities `d u v ≤ ε`; bounding all of them makes every pair an edge (full
  simplex), while strictly violating all of them kills every edge (discrete).  The
  independence complex is literally the clique complex of the complement, so the
  entire base theory dualizes by substituting `Gᶜ`.
Failure analysis: the "discrete" direction needs *strict* separation `ε < d u v`;
  with only `ε ≤ d u v` a boundary pair could still be an edge, so the threshold
  characterization would fail at the critical scale.
-- !-- Lab Notebook -- !--
-/

namespace CliqueComplexFlag

open scoped Classical

universe u
variable {V : Type u}

/-! ## The two extremes of the Vietoris–Rips filtration -/



/-! ## The independence complex and complement duality -/

/-- The **independence complex** `independenceComplex G`: faces are the finite
*independent* sets of `G` (no two distinct elements adjacent). -/
def independenceComplex (G : SimpleGraph V) : ASC V where
  faces := {s : Finset V | G.IsIndepSet (↑s : Set V)}
  down_closed := by
    intro s t hst ht
    exact ht.mono (by exact_mod_cast hst)




end CliqueComplexFlag


