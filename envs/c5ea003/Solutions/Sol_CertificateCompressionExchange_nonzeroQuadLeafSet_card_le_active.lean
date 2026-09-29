-- Prove2me | solution 1 for CertificateCompressionExchange.nonzeroQuadLeafSet_card_le_active
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:06:00.636025+00:00
-- url     : https://prove2.me/submissions/93cddea0-47a9-4cd4-acb5-358fdbf1e5be

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

/-- Independent sets use only active variables. -/
theorem indep_subset_active {n r : ℕ} (F : BasisFamily n r)
    {I : Finset (Fin n)} (hI : F.IsIndep I) :
    I ⊆ F.activeVars := by
  intro x hx
  obtain ⟨B, hB, hIB⟩ := hI
  exact Finset.subset_biUnion_of_mem id hB (hIB hx)



/-! ## Part IX: Structural Properties -/




/-! ## Part X: Verified Algorithm -/





/-! ## Part XI: Monomial Derivative Vanishing -/



/-! ## Part XII: Exchange Geometry Connection -/



/-! ## Part XIII: Compression Ratio Analysis -/





open CertificateCompressionExchange in
theorem solution{n r : ℕ}
    (F : BasisFamily n r) (k : ℕ) :
    supportCompressedLeafCount F.bases k ≤
      Nat.choose F.activeVarCount k := by
  unfold supportCompressedLeafCount NonzeroQuadraticLeafSet
  show F.indepCount k ≤ _
  have h_sub : F.indepSets k ⊆ F.activeVars.powersetCard k := by
    intro I hI
    simp only [BasisFamily.indepSets, Finset.mem_filter, Finset.mem_powersetCard] at hI ⊢
    exact ⟨indep_subset_active F hI.2, hI.1.2⟩
  calc F.indepCount k
      = (F.indepSets k).card := rfl
    _ ≤ (F.activeVars.powersetCard k).card := Finset.card_le_card h_sub
    _ = Nat.choose F.activeVarCount k := by
        simp [BasisFamily.activeVarCount, Finset.card_powersetCard]
