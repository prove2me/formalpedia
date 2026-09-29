-- Prove2me | Definitions.Def_Bridges_GraphTheory_CertificateCompressionExchange
-- name    : Bridges_GraphTheory_CertificateCompressionExchange
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:22:20.128129+00:00
-- url     : https://prove2.me/theorems/5abf114a-3c17-4960-931a-3acc1da22ecd
-- title:
--   Aether Catalog definitions — Bridges_GraphTheory_CertificateCompressionExchange
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.GraphTheory.CertificateCompressionExchange`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/GraphTheory/CertificateCompressionExchange.lean by skeleton subtraction
import Mathlib
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

namespace CertificateCompressionExchange

/-! ## Part I: Multiaffine Finsupp Geometry -/

/-- A finsupp is multiaffine if all values are at most 1. -/
def IsMultiaffine {n : ℕ} (β : Fin n →₀ ℕ) : Prop :=
  ∀ i : Fin n, β i ≤ 1

/-- The support of a finsupp as a Finset of indices where the value is nonzero. -/
def finsuppSupp {n : ℕ} (β : Fin n →₀ ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun i => β i ≠ 0

/-- The indicator finsupp of a Finset: maps elements to 1, rest to 0. -/
def indicatorFinsupp {n : ℕ} (S : Finset (Fin n)) : Fin n →₀ ℕ :=
  Finsupp.indicator S (fun _ _ => 1)








/-! ## Part II: Basis Family Abstraction -/

/-- A basis family: a nonempty collection of r-element subsets of Fin n.
This abstracts the basis system of a matroid. -/
structure BasisFamily (n r : ℕ) where
  /-- The collection of bases -/
  bases : Finset (Finset (Fin n))
  /-- Every basis has exactly r elements -/
  bases_card : ∀ B ∈ bases, B.card = r
  /-- The basis family is nonempty -/
  bases_nonempty : bases.Nonempty

/-- A set is independent if it is contained in some basis. -/
def BasisFamily.IsIndep {n r : ℕ} (F : BasisFamily n r) (I : Finset (Fin n)) : Prop :=
  ∃ B ∈ F.bases, I ⊆ B

instance {n r : ℕ} (F : BasisFamily n r) (I : Finset (Fin n)) :
    Decidable (F.IsIndep I) :=
  inferInstanceAs (Decidable (∃ B ∈ F.bases, I ⊆ B))

/-- The set of independent k-sets. -/
def BasisFamily.indepSets {n r : ℕ} (F : BasisFamily n r) (k : ℕ) :
    Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard k).filter fun I => F.IsIndep I

/-- The count of independent k-sets. -/
def BasisFamily.indepCount {n r : ℕ} (F : BasisFamily n r) (k : ℕ) : ℕ :=
  (F.indepSets k).card

/-- Active variables: those appearing in at least one basis. -/
def BasisFamily.activeVars {n r : ℕ} (F : BasisFamily n r) : Finset (Fin n) :=
  F.bases.biUnion id

/-- Active variable count. -/
def BasisFamily.activeVarCount {n r : ℕ} (F : BasisFamily n r) : ℕ :=
  F.activeVars.card

/-! ## Part III: New Concept — Nonzero Quadratic Leaf Set -/

/-- The **nonzero quadratic leaf set**: the family of k-element subsets I of
Fin n such that some basis B contains I. This is the support-theoretic
notion of which derivative branches survive in the Lorentzian recognition tree.

For a multiaffine homogeneous polynomial of degree r with support s,
a degree-(r-2) derivative ∂^α p is nonzero iff supp(α) ⊆ supp(β) for
some β ∈ s. When s consists of basis indicator vectors, this reduces
to I being independent. -/
def NonzeroQuadraticLeafSet {n : ℕ}
    (bases : Finset (Finset (Fin n))) (k : ℕ) : Finset (Finset (Fin n)) :=
  (Finset.univ.powersetCard k).filter fun I => ∃ B ∈ bases, I ⊆ B

/-- The support-compressed leaf count. -/
def supportCompressedLeafCount {n : ℕ}
    (bases : Finset (Finset (Fin n))) (k : ℕ) : ℕ :=
  (NonzeroQuadraticLeafSet bases k).card

/-! ## Part IV: New Concept — Basis Indicator Support -/

/-- The **basis indicator support**: indicator finsupps of the bases.
This bridges the combinatorial world to the algebraic world. -/
def basisIndicatorSupport {n r : ℕ}
    (F : BasisFamily n r) : Finset (Fin n →₀ ℕ) :=
  F.bases.image indicatorFinsupp



/-! ## Part V: New Concept — Nonzero Derivative Profile -/


/-! ## Part VI: Core Theorems -/





/-! ## Part VII: Uniform Matroid -/

/-- The uniform basis family: all r-element subsets are bases. -/
def uniformBasisFamily (n r : ℕ) (hrn : r ≤ n) : BasisFamily n r where
  bases := Finset.univ.powersetCard r
  bases_card B hB := (Finset.mem_powersetCard.mp hB).2
  bases_nonempty := by
    rw [Finset.powersetCard_nonempty]
    simp [Fintype.card_fin]; omega




/-! ## Part VIII: Support Compression Bound -/




/-! ## Part IX: Structural Properties -/




/-! ## Part X: Verified Algorithm -/

/-- Count nonzero quadratic leaves from basis family data,
without polynomial differentiation. -/
def countNonzeroQuadraticLeavesFromBases {n r : ℕ}
    (F : BasisFamily n r) : ℕ :=
  F.indepCount (r - 2)




/-! ## Part XI: Monomial Derivative Vanishing -/



/-! ## Part XII: Exchange Geometry Connection -/

/-- The basis exchange property: for any two bases B₁, B₂ and any
i ∈ B₁ \ B₂, there exists j ∈ B₂ \ B₁ such that (B₁ \ {i}) ∪ {j}
is also a basis. -/
def BasisFamily.HasExchange {n r : ℕ} (F : BasisFamily n r) : Prop :=
  ∀ B₁ ∈ F.bases, ∀ B₂ ∈ F.bases,
    ∀ i ∈ B₁, i ∉ B₂ →
    ∃ j ∈ B₂, j ∉ B₁ ∧ ((B₁.erase i) ∪ {j}) ∈ F.bases


/-! ## Part XIII: Compression Ratio Analysis -/

/-- The compression ratio: actual / ambient worst case. -/
def compressionRatio {n r : ℕ} (F : BasisFamily n r) : ℚ :=
  if Nat.choose n (r - 2) = 0 then 0
  else (F.indepCount (r - 2) : ℚ) / (Nat.choose n (r - 2) : ℚ)



end CertificateCompressionExchange


