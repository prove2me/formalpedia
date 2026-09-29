-- Prove2me | solution 1 for CliqueComplexFlag.vietorisRips_discrete_of_separated
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:52:42.713282+00:00
-- url     : https://prove2.me/submissions/a5beadfb-78fa-4a59-9c7e-a66025b61a05

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
theorem solution{d : V → V → ℝ} {ε : ℝ}
    (h : ∀ u v, u ≠ v → ε < d u v) (s : Finset V) :
    s ∈ (vietorisRips d ε).faces ↔ s.card ≤ 1 := by
  -- !-- a set of size ≥ 2 contains a distinct pair, which cannot be an edge since
  --     `ε < d u v` contradicts `d u v ≤ ε`; sets of size ≤ 1 are vacuously cliques. -- !--
  rw [vietorisRips, mem_cliqueComplex, SimpleGraph.isClique_iff]
  constructor
  · intro hclique
    by_contra hcard
    rw [not_le] at hcard
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 hcard
    obtain ⟨_, h1, _⟩ := hclique (by exact_mod_cast hu) (by exact_mod_cast hv) huv
    exact absurd h1 (not_le.2 (h u v huv))
  · intro hcard u hu v hv huv
    exfalso
    have : 2 ≤ s.card := by
      apply Finset.one_lt_card.2
      exact ⟨u, by exact_mod_cast hu, v, by exact_mod_cast hv, huv⟩
    omega
