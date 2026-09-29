-- Prove2me | solution 1 for CertificateCompressionExchange.uniform_has_exchange
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:06:01.097307+00:00
-- url     : https://prove2.me/submissions/2eb46123-65e7-4d73-971f-d6837c551b4d

-- Sol generated from Bridges/GraphTheory/CertificateCompressionExchange.lean
import Mathlib
import Definitions.Def_Bridges_GraphTheory_CertificateCompressionExchange
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Certificate Compression by Exchange Geometry

This file develops the theory of **certificate compression for Lorentzian
recognition** of matroid basis generating polynomials. The central insight is
that the recursion tree for recognizing Lorentzian polynomials collapses for
matroid basis polynomials because nonzero quadratic derivative leaves are in
bijection with independent sets — a consequence of multiaffine support geometry.

## Core Mathematical Statement

For a rank-r matroid M on ground set [n], the basis generating polynomial
  B_M(x₁,…,xₙ) = Σ_{B ∈ bases(M)} ∏_{i ∈ B} xᵢ
has the property that the iterated partial derivative ∂^α B_M is nonzero
if and only if supp(α) is an independent set of M. Hence the number of
nonzero quadratic leaves (|α| = r-2) equals the number of independent
(r-2)-sets.

## Main New Concepts

* `NonzeroQuadraticLeafSet` — The support-theoretic set of surviving derivative branches
* `basisIndicatorSupport` — Basis indicator vectors as finsupp support
* `NonzeroDerivProfile` — Which derivative indices survive at the multiindex level

## Main Theorems

* `derivative_survival_iff_independent` — Derivative survival = matroid independence
* `nonzeroQuadLeafSet_eq_indepSets` — Leaf set = independent set family
* `nonzeroQuadLeafSet_card_uniformMatroid` — Uniform matroid closed form C(n, r-2)
* `nonzeroQuadLeafSet_card_le_active` — Support compression upper bound
* `multiaffine_derivative_zero_of` — Monomial derivative vanishing criterion
* `indepCount_mono` — Monotonicity of independent set counts
* `countFromBases_eq_card` — Verified algorithm correctness

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
* Murota, "Discrete Convex Analysis", SIAM, 2003
-/

open Finset BigOperators

noncomputable section

open CertificateCompressionExchange

/-! ## Part I: Multiaffine Finsupp Geometry -/











/-! ## Part II: Basis Family Abstraction -/








/-! ## Part III: New Concept — Nonzero Quadratic Leaf Set -/



/-! ## Part IV: New Concept — Basis Indicator Support -/




/-! ## Part V: New Concept — Nonzero Derivative Profile -/


/-! ## Part VI: Core Theorems -/





/-! ## Part VII: Uniform Matroid -/





/-! ## Part VIII: Support Compression Bound -/




/-! ## Part IX: Structural Properties -/




/-! ## Part X: Verified Algorithm -/





/-! ## Part XI: Monomial Derivative Vanishing -/



/-! ## Part XII: Exchange Geometry Connection -/



/-! ## Part XIII: Compression Ratio Analysis -/





open CertificateCompressionExchange in
theorem solution{n r : ℕ} (hrn : r ≤ n) (_hr : 0 < r) :
    (uniformBasisFamily n r hrn).HasExchange := by
  intro B₁ hB₁ B₂ hB₂ i hiB₁ hiB₂
  have hB₁card := (Finset.mem_powersetCard.mp hB₁).2
  have hB₂card := (Finset.mem_powersetCard.mp hB₂).2
  -- B₂ \ B₁ is nonempty
  have hne : (B₂ \ B₁).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hsub := Finset.sdiff_eq_empty_iff_subset.mp hempty
    have heq : B₂ = B₁ := Finset.eq_of_subset_of_card_le hsub (by omega)
    rw [heq] at hiB₂; exact hiB₂ hiB₁
  obtain ⟨j, hj⟩ := hne
  rw [Finset.mem_sdiff] at hj
  obtain ⟨hjB₂, hjB₁⟩ := hj
  refine ⟨j, hjB₂, hjB₁, ?_⟩
  simp only [uniformBasisFamily, Finset.mem_powersetCard]
  refine ⟨Finset.subset_univ _, ?_⟩
  have hdisjoint : Disjoint (B₁.erase i) {j} := by
    rw [Finset.disjoint_singleton_right]
    exact fun h => hjB₁ (Finset.mem_of_mem_erase h)
  rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_singleton,
      Finset.card_erase_of_mem hiB₁, hB₁card]
  omega
