-- Prove2me | Theorems.Thm_CliqueComplexFlag_mem_independenceComplex
-- name    : CliqueComplexFlag.mem_independenceComplex
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:09:23.37019+00:00
-- url     : https://prove2.me/theorems/befa8e88-8f1e-45e2-b87e-25afaf6347f3
-- title:
--   Complement duality: a set is a face of `independenceComplex G` iff it is a
-- statement:
--   **Complement duality:** a set is a face of `independenceComplex G` iff it is a
--   face of `cliqueComplex Gᶜ`.  Independence in `G` is exactly cliqueness in `Gᶜ`.
--
--   ```lean
--   theorem CliqueComplexFlag.mem_independenceComplex{G : SimpleGraph V} {s : Finset V} :
--       s ∈ (independenceComplex G).faces ↔ s ∈ (cliqueComplex Gᶜ).faces := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RamseyTheory/CliqueComplexVietorisRips.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RamseyTheory/CliqueComplexVietorisRips.lean#L90

-- Thm stub generated from Geometry/RamseyTheory/CliqueComplexVietorisRips.lean
import Mathlib
import Definitions.Def_Geometry_RamseyTheory_CliqueComplexFlag
import Definitions.Def_Geometry_RamseyTheory_CliqueComplexVietorisRips
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

open CliqueComplexFlag

open scoped Classical

universe u
variable {V : Type u}

/-! ## The two extremes of the Vietoris–Rips filtration -/



/-! ## The independence complex and complement duality -/

theorem CliqueComplexFlag.mem_independenceComplex{G : SimpleGraph V} {s : Finset V} :
    s ∈ (independenceComplex G).faces ↔ s ∈ (cliqueComplex Gᶜ).faces := by sorry
