-- Prove2me | solution 1 for MagnitudeTope.cayleyCycles22_nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T10:15:53.641234+00:00
-- url     : https://prove2.me/submissions/090bd8b2-f58d-4f63-adbe-dd750d980e20

-- Sol generated from Geometry/MagnitudeTopeGraphs.lean
import Mathlib
import Definitions.Def_Geometry_MagnitudeTopeGraphs
import Theorems.Thm_MagnitudeTope_cayleyGraph_connected
import Theorems.Thm_MagnitudeTope_diagIncl_range_le_ker
/-
# Magnitude homology of tope graphs

This file develops, from scratch, a chain of results around the magnitude homology of
*tope graphs* of real hyperplane arrangements, following the theme of the paper
"Magnitude homology of tope graphs".

The development is organised as a strictly increasing chain of results, each one using
the previous ones:

1. **The coordinate (Boolean) arrangement.** For the real arrangement of the `n`
   coordinate hyperplanes `{x : xᵢ = 0}` in `ℝⁿ`, the chambers (topes) are indexed by
   subsets `s ⊆ Fin n` (the set of coordinates that are positive). We prove that these
   chambers are nonempty, convex, pairwise disjoint, avoid all hyperplanes, and — the key
   combinatorial fact — that the set of hyperplanes *separating* two chambers is exactly
   the symmetric difference of the indexing sets.

2. **The tope graph.** Two topes are adjacent when exactly one hyperplane separates them.
   We prove that the graph distance of the resulting tope graph is exactly the number of
   separating hyperplanes, `dist s t = |s Δ t|`, and deduce connectivity.

3. **Magnitude chains in low degree.** For an arbitrary connected simple graph `G` we
   introduce the magnitude chain generators in degrees 1 and 2 and the magnitude
   differential `δ₂`, and prove:
   * `Gen2` is empty in lengths `< 2` (chains are "long"),
   * hence `MH_{1,1}(G)` is the free abelian group on the ordered edges of `G`,
   * `δ₂` is surjective in every length `ℓ ≥ 2`, hence `MH_{1,ℓ}(G) = 0`.
   The last statement is the degree-1 case of *diagonality*, which the paper establishes
   in all degrees for tope graphs.

4. **Diagonal cycles in bidegree (2,2).** The ordered edges of `G` embed into the cycles
   `ker δ₂` in length 2 via `(x,y) ↦ (x,y,x)`.

5. **Application to the tope graph.** Combining everything: for the coordinate
   arrangement in `ℝⁿ` the tope graph is connected, `MH_{1,1}` is free of rank `2ⁿ · n`,
   `MH_{1,ℓ} = 0` for `ℓ ≥ 2`, and the group of `(2,2)`-cycles is nontrivial for `n ≥ 1`.
   We also count the chain groups: `MC_{1,ℓ}` has rank `2ⁿ · C(n,ℓ)` and `MC_{2,2}` has
   rank `2ⁿ · n²`, and we exhibit the splitting
   `MH_{2,2} ⊕ ℤ^{2ⁿ·C(n,2)} ≅ ℤ^{2ⁿ·n²}` — i.e. `MH_{2,2}` has rank `2ⁿ · n(n+1)/2`,
   which is `2ⁿ` times the value at `2` of the Hilbert function of a polynomial ring in
   `n` variables, as predicted by the Stanley–Reisner description.

6. **The Coxeter picture.** The coordinate arrangement is the reflection arrangement of
   the Coxeter group `(ℤ/2)ⁿ` (type `A₁ⁿ`). We prove that graph isomorphisms are
   isometries, that the tope graph is isomorphic to the Cayley graph of `(ℤ/2)ⁿ` with
   respect to its Coxeter generators, and transport all the magnitude homology
   computations of stage 5 to that Cayley graph.

Everything below is self-contained (only `Mathlib` is imported).
-/


open MagnitudeTope

open scoped Classical

/-! ## 1. Chambers of the coordinate arrangement in `ℝⁿ` -/


variable {n : ℕ}









/-! ## 2. The tope graph and its distance function -/


variable {n : ℕ}










/-! ## 3. Magnitude chains and magnitude homology in degree 1 -/


variable {V : Type*} {G : SimpleGraph V}


















/-! ## 4. Diagonal cycles in bidegree `(2,2)` -/


variable {V : Type*} {G : SimpleGraph V}


lemma diagGen_injective : Function.Injective (diagGen (G := G)) := by
  rintro ⟨⟨x, y⟩, hx⟩ ⟨⟨x', y'⟩, hx'⟩ h
  have h' : ((x, y, x) : V × V × V) = (x', y', x') := congrArg Subtype.val h
  simp only [Prod.mk.injEq] at h'
  simp [h'.1, h'.2.1]


lemma diagIncl_injective (G : SimpleGraph V) : Function.Injective (diagIncl G) :=
  Finsupp.mapDomain_injective diagGen_injective


/-- **Diagonal cycles in bidegree (2,2).** The ordered edges of a connected graph give a
free subgroup of the group of `(2,2)`-cycles. -/
theorem exists_free_subgroup_of_cycles (hG : G.Connected) :
    ∃ φ : (Gen1 G 1 →₀ ℤ) →ₗ[ℤ] (Gen2 G 2 →₀ ℤ),
      Function.Injective φ ∧ LinearMap.range φ ≤ LinearMap.ker (delta2 hG 2) :=
  ⟨diagIncl G, diagIncl_injective G, diagIncl_range_le_ker hG⟩


/-! ## 5. Application: magnitude homology of the tope graph -/


variable {n : ℕ}












/-! ## 6. The Coxeter group `(ℤ/2)ⁿ` and its Cayley graph -/





variable {n : ℕ}


















open MagnitudeTope in
theorem solution(n : ℕ) (hn : 0 < n) :
    LinearMap.ker (delta2 (cayleyGraph_connected n) 2) ≠ ⊥ := by
  obtain ⟨φ, hinj, hle⟩ := exists_free_subgroup_of_cycles (cayleyGraph_connected n)
  set a : Gen1 (cayleyGraph n) 1 :=
    genEquiv1 (topeIsoCayley n) 1
      ((Gen1_one_equiv (topeGraph n)).symm ⟨(∅, symmDiff ∅ {(⟨0, hn⟩ : Fin n)}),
        tope_adj_flip ∅ ⟨0, hn⟩⟩) with ha
  intro hbot
  have h0 : φ (Finsupp.single a 1) = 0 := by
    have hmem : φ (Finsupp.single a 1) ∈ LinearMap.ker (delta2 (cayleyGraph_connected n) 2) :=
      hle ⟨_, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  have hz : Finsupp.single a (1 : ℤ) = 0 := hinj (by simpa using h0)
  simp [Finsupp.single_eq_zero] at hz
