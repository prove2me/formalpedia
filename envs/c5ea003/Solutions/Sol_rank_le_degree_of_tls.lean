-- Prove2me | solution 1 for rank_le_degree_of_tls
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T08:40:57.365981+00:00
-- url     : https://prove2.me/submissions/3f2deb6f-4df8-4864-b281-ed1fd9ea2151

-- Sol generated from Geometry/TropicalAlgebra/TropicalBrillNoether.lean
import Mathlib
import Definitions.Def_Geometry_TropicalAlgebra_TropicalBrillNoether
/-
# Tropical Brill-Noether Theory

Formalization of the Brill-Noether number and divisor theory on graphs,
connecting tropical geometry to classical algebraic geometry.
-/

/-! ## Section 1: The Brill-Noether Number -/













/-! ## Section 2: Graph Divisors -/




/-- An effective divisor has non-negative degree. -/
theorem effective_nonneg_degree {V : Type*} [Fintype V]
    (D : GraphDivisor V) (hD : isEffective D) : 0 ≤ divisorDegree D :=
  Finset.sum_nonneg (fun v _ => hD v)

/-! ## Section 3: Chip-Firing -/



/-
The Laplacian action sums to zero.
-/
theorem laplacian_sum_zero {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (f : V → ℤ) :
    ∑ v : V, laplacianAction G f v = 0 := by
  unfold laplacianAction
  simp +decide [Finset.sum_ite]
  simp +decide [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp +decide [Finset.sum_ite, SimpleGraph.adj_comm]

/-- Linear equivalence preserves degree. -/
theorem linEquiv_preserves_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D₁ D₂ : GraphDivisor V) (h : linEquiv G D₁ D₂) :
    divisorDegree D₁ = divisorDegree D₂ := by
  obtain ⟨f, hf⟩ := h
  have key : ∑ v : V, D₂ v = ∑ v : V, (D₁ v + laplacianAction G f v) :=
    Finset.sum_congr rfl (fun v _ => hf v)
  simp only [divisorDegree]
  linarith [Finset.sum_add_distrib (f := fun v => D₁ v) (g := laplacianAction G f)
    (s := Finset.univ (α := V)), laplacian_sum_zero G f, key]


/-! ## Section 4: Tropical Linear Series (Novel Definition) -/



/-! ## Section 5: Graph Genus -/



/-! ## Section 6: Reduced Divisors -/



/-! ## Section 7: Rank-Degree Inequality -/

/-- A point-mass divisor has the expected degree. -/
theorem pointMass_degree {V : Type*} [Fintype V] [DecidableEq V] (v₀ : V) (n : ℤ) :
    divisorDegree (fun v => if v = v₀ then n else 0) = n := by
  simp [divisorDegree, Finset.sum_ite_eq']

/-- A point-mass divisor with n ≥ 0 is effective. -/
theorem pointMass_effective {V : Type*} [DecidableEq V] (v₀ : V) (n : ℤ) (hn : 0 ≤ n) :
    isEffective (fun v => if v = v₀ then n else 0) := by
  intro v; simp only; split <;> omega

/-- The degree of D - E as a pointwise function. -/
theorem degree_sub {V : Type*} [Fintype V]
    (D E : GraphDivisor V) :
    divisorDegree (fun v => D v - E v) = divisorDegree D - divisorDegree E := by
  simp [divisorDegree, sub_eq_add_neg, Finset.sum_add_distrib, Finset.sum_neg_distrib]


/-! ## Section 8: Concrete Results -/





/-! ## Section 9: Conjecture -/




theorem solution{V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (L : TropicalLinearSeries V G) [Nonempty V] :
    L.rank ≤ L.deg := by
  -- Construct E = point mass of rank chips at an arbitrary vertex
  obtain ⟨v₀⟩ := ‹Nonempty V›
  let E : GraphDivisor V := fun v => if v = v₀ then L.rank else 0
  have hE_eff : isEffective E := pointMass_effective v₀ L.rank L.rank_nonneg
  have hE_deg : divisorDegree E = L.rank := pointMass_degree v₀ L.rank
  have hE_le : divisorDegree E ≤ L.rank := le_of_eq hE_deg
  -- By rank_witness, D - E ~ D' effective
  obtain ⟨D', hD'_equiv, hD'_eff⟩ := L.rank_witness E hE_eff hE_le
  -- D' effective ⇒ deg(D') ≥ 0
  have hD'_deg : 0 ≤ divisorDegree D' := effective_nonneg_degree D' hD'_eff
  -- Linear equiv preserves degree: deg(D - E) = deg(D')
  have hpres := linEquiv_preserves_degree G _ D' hD'_equiv
  -- deg(D - E) = deg(D) - deg(E) = deg - rank
  rw [degree_sub] at hpres
  linarith [L.deg_eq, hE_deg]
