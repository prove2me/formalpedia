-- Prove2me | solution 1 for CliqueComplexFlag.mem_independenceComplex
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:52:41.710315+00:00
-- url     : https://prove2.me/submissions/10d65a58-38ed-4fc5-92ce-bdf03aaf42d7

-- Sol generated from Geometry/RamseyTheory/CliqueComplexVietorisRips.lean
import Mathlib
import Definitions.Def_Geometry_RamseyTheory_CliqueComplexFlag
import Definitions.Def_Geometry_RamseyTheory_CliqueComplexVietorisRips
import Theorems.Thm_CliqueComplexFlag_mem_cliqueComplex
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






open CliqueComplexFlag in
theorem solution{G : SimpleGraph V} {s : Finset V} :
    s ∈ (independenceComplex G).faces ↔ s ∈ (cliqueComplex Gᶜ).faces := by
  -- !-- `G.IsIndepSet s ↔ Gᶜ.IsClique s`, by unfolding `compl_adj`. -- !--
  simp only [independenceComplex, mem_cliqueComplex, Set.mem_setOf_eq]
  unfold SimpleGraph.IsIndepSet SimpleGraph.IsClique Set.Pairwise
  constructor
  · intro hind a ha b hb hab
    rw [SimpleGraph.compl_adj]
    exact ⟨hab, hind ha hb hab⟩
  · intro hcl a ha b hb hab
    have := hcl ha hb hab
    rw [SimpleGraph.compl_adj] at this
    exact this.2
