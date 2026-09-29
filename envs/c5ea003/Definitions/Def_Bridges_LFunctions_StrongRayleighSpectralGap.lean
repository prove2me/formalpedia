-- Prove2me | Definitions.Def_Bridges_LFunctions_StrongRayleighSpectralGap
-- name    : Bridges_LFunctions_StrongRayleighSpectralGap
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:28:34.80597+00:00
-- url     : https://prove2.me/theorems/ffb20a38-f630-40fe-a83d-b15881a09580
-- title:
--   Aether Catalog definitions — Bridges_LFunctions_StrongRayleighSpectralGap
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.LFunctions.StrongRayleighSpectralGap`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/LFunctions/StrongRayleighSpectralGap.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.
-/

/-!
# Strong Rayleigh Property and Spectral Gap Certificates

This file formalizes a new bridge between Lorentzian/Hodge-theoretic curvature
and quantitative Markov-chain mixing for basis exchange walks on matroids.
The central insight is that Hessian-signature certificates from the theory of
Lorentzian polynomials can be converted into Poincaré inequalities and
spectral-gap lower bounds.

## Mathematical Overview

The Brändén–Huh theory of Lorentzian polynomials established that certain
polynomials (including basis-generating polynomials of matroids) satisfy a
"reversed Cauchy–Schwarz" inequality coming from the Hessian having at most
one positive eigenvalue. We formalize the passage from this algebraic
condition to stochastic convergence guarantees:

1. **Curvature → Poincaré**: A "curvature constant" κ extracted from the
   Hessian signature gives Var_μ(f) ≤ κ⁻¹ · E(f,f).
2. **Rank-scale bound**: Under a normalization hypothesis, κ ≥ C/r(M).
3. **Truncated certificates**: Depth-k refinements approximate the true
   spectral gap to within ε when k ≥ C·r·log(1/ε).
4. **Cross-domain abstraction**: The "curvature-controlled kernel" framework
   applies beyond matroids to any finite reversible chain with a curvature
   certificate.

## References

* Brändén–Huh, "Lorentzian Polynomials", Annals of Mathematics, 2020
* Anari–Liu–Oveis Gharan–Vinzant, "Log-Concave Polynomials", 2019
* Diaconis–Saloff-Coste, "Comparison Theorems for Reversible Markov Chains", 1993
-/

open Finset BigOperators Real

noncomputable section

/-! ## Section 1: Finite Probability and Variance -/

/-- A finite probability mass function on a type Ω. -/
structure FinPMF (Ω : Type*) [Fintype Ω] where
  mass : Ω → ℝ
  mass_nonneg : ∀ x, 0 ≤ mass x
  mass_sum : ∑ x : Ω, mass x = 1

namespace FinPMF

variable {Ω : Type*} [Fintype Ω]

/-- Expected value under the distribution. -/
def expect (μ : FinPMF Ω) (f : Ω → ℝ) : ℝ :=
  ∑ x : Ω, μ.mass x * f x

/-- Variance under the distribution: Var(f) = E[(f - E[f])²]. -/
def variance (μ : FinPMF Ω) (f : Ω → ℝ) : ℝ :=
  μ.expect (fun x => (f x - μ.expect f) ^ 2)


/-- A function is orthogonal to constants if its expectation is zero. -/
def IsOrthToConst (μ : FinPMF Ω) (f : Ω → ℝ) : Prop :=
  μ.expect f = 0

end FinPMF

/-! ## Section 2: Dirichlet Forms -/

/-- Dirichlet form: E(f,f) = (1/2) ∑_{x,y} μ(x) P(x,y) (f(x) - f(y))². -/
def dirichletFormFromKernel {Ω : Type*} [Fintype Ω]
    (μ : FinPMF Ω) (P : Ω → Ω → ℝ) (f : Ω → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x : Ω, ∑ y : Ω, μ.mass x * P x y * (f x - f y) ^ 2




/-! ## Section 3: Spectral Gap Definition -/

/-- The spectral gap is at least γ if Var(f) ≤ γ⁻¹ · E(f,f) for all f. -/
def hasSpectralGapAtLeast {Ω : Type*} [Fintype Ω]
    (μ : FinPMF Ω) (P : Ω → Ω → ℝ) (γ : ℝ) : Prop :=
  ∀ f : Ω → ℝ, μ.variance f ≤ γ⁻¹ * dirichletFormFromKernel μ P f


/-! ## Section 4: Curvature-Controlled Kernels (Cross-Domain Abstraction) -/

/-- A **curvature-controlled kernel** is a finite reversible Markov kernel
    equipped with a curvature constant κ > 0 such that a Poincaré inequality
    holds with constant 1/κ.

    This abstracts the phenomenon away from matroids: any finite stochastic
    process with "negative curvature" in an appropriate algebraic sense
    satisfies rapid mixing.

    Applications: matroid basis exchange, determinantal processes,
    high-dimensional expander walks, exclusion processes. -/
structure CurvatureControlledKernel (Ω : Type*) [Fintype Ω] where
  μ : FinPMF Ω
  P : Ω → Ω → ℝ
  P_nonneg : ∀ x y, 0 ≤ P x y
  curvatureConst : ℝ
  curvatureConst_pos : 0 < curvatureConst
  poincare_from_curvature :
    ∀ f : Ω → ℝ,
      μ.variance f ≤ curvatureConst⁻¹ * dirichletFormFromKernel μ P f

namespace CurvatureControlledKernel

variable {Ω : Type*} [Fintype Ω]



end CurvatureControlledKernel

/-! ## Section 5: Exchange Systems -/

/-- An **exchange system** abstracts the structure of matroid bases:
    a finite set of basis states with exchange neighbors, equipped with
    a uniform distribution and a basis exchange walk. -/
structure ExchangeSystem where
  numStates : ℕ
  numStates_pos : 0 < numStates
  rank : ℕ
  rank_pos : 0 < rank
  kernel : Fin numStates → Fin numStates → ℝ
  kernel_nonneg : ∀ i j, 0 ≤ kernel i j

namespace ExchangeSystem

/-- The uniform distribution. -/
def uniformDist (E : ExchangeSystem) : FinPMF (Fin E.numStates) where
  mass _ := (1 : ℝ) / E.numStates
  mass_nonneg _ := by positivity
  mass_sum := by
    simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    rw [one_div, mul_inv_cancel₀]
    exact Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp E.numStates_pos)

/-- Dirichlet form of the exchange walk. -/
def dirichletForm (E : ExchangeSystem) (f : Fin E.numStates → ℝ) : ℝ :=
  dirichletFormFromKernel E.uniformDist E.kernel f

/-- Variance under the uniform distribution. -/
def var (E : ExchangeSystem) (f : Fin E.numStates → ℝ) : ℝ :=
  E.uniformDist.variance f

end ExchangeSystem

/-! ## Section 6: Lorentzian Exchange Certificates -/

/-- A **Lorentzian exchange certificate** packages the data that the
    Hessian-signature analysis of the basis-generating polynomial
    yields a Poincaré inequality with explicit constant κ. -/
structure HasLorentzianExchangeCertificate (E : ExchangeSystem) where
  certConst : ℝ
  certConst_pos : 0 < certConst
  exchangeBound :
    ∀ f : Fin E.numStates → ℝ,
      E.var f ≤ certConst⁻¹ * E.dirichletForm f

namespace HasLorentzianExchangeCertificate

variable {E : ExchangeSystem}



end HasLorentzianExchangeCertificate

/-! ## Section 7: Exchange Systems as Curvature-Controlled Kernels -/


/-! ## Section 8: Normalized Certificates and Rank-Scale Bound -/

/-- Universal gap constant C > 0 for the rank-scale bound. -/
def universalGapConstant : ℝ := 1


/-- A **normalized Lorentzian certificate** ensures κ ≥ C/r. -/
structure NormalizedLorentzianCertificate (E : ExchangeSystem) extends
    HasLorentzianExchangeCertificate E where
  rankScaled : universalGapConstant / (E.rank : ℝ) ≤ certConst


/-! ## Section 9: Truncated Certificate Systems -/

/-- A **truncated certificate system** provides a monotone sequence of
    lower bounds on the spectral gap with geometric error decay. -/
structure TruncatedCertificateSystem (E : ExchangeSystem) where
  lowerBound : ℕ → ℝ
  lowerBound_nonneg : ∀ k, 0 ≤ lowerBound k
  lowerBound_mono : Monotone lowerBound
  lowerBound_sound :
    ∀ k, hasSpectralGapAtLeast E.uniformDist E.kernel (lowerBound k)
  baseCert : HasLorentzianExchangeCertificate E
  contractionRate : ℝ
  contractionRate_pos : 0 < contractionRate
  contractionRate_lt_one : contractionRate < 1
  error_decay : ∀ k,
    baseCert.certConst - lowerBound k ≤ baseCert.certConst * contractionRate ^ k

namespace TruncatedCertificateSystem

variable {E : ExchangeSystem}

/-
**Theorem C**: Truncated certificates approximate the spectral gap.
    For any ε > 0, there exists depth k such that κ - κ_k ≤ ε.
-/

end TruncatedCertificateSystem

/-! ## Section 10: Verified Truncated Gap Computation -/

/-- Compute the truncated gap lower bound: κ · (1 - ρ^k). -/
def computeTruncatedGapBound (κ ρ : ℝ) (k : ℕ) : ℝ :=
  κ * (1 - ρ ^ k)


/-
The computed bound is monotone in k.
-/

/-
The computed bound is at most κ.
-/

/-
**Soundness**: The computed bound is a valid spectral gap lower bound.
    Since computeTruncatedGapBound κ ρ k ≤ κ and the certificate gives
    Var(f) ≤ κ⁻¹ · E(f,f), weakening gives Var(f) ≤ κ_k⁻¹ · E(f,f).
-/

/-! ## Section 11: Mixing Time -/


/-
For rank-r systems with gap ≥ C/r, mixing time is O(r · log(N/ε)).
-/

/-! ## Section 12: Partition Matroid Data -/

/-- A partition matroid specified by block sizes. -/
structure PartitionMatroidData where
  numBlocks : ℕ
  numBlocks_pos : 0 < numBlocks
  blockSize : Fin numBlocks → ℕ
  blockSize_ge_two : ∀ i, 2 ≤ blockSize i

namespace PartitionMatroidData

/-- Number of bases = product of block sizes. -/
def numBases (P : PartitionMatroidData) : ℕ :=
  ∏ i : Fin P.numBlocks, P.blockSize i



end PartitionMatroidData

/-! ## Section 13: Poincaré from Mean-Zero Bound -/

/-
If the Poincaré inequality holds for mean-zero functions, it holds for all.
-/

/-! ## Section 14: Conjectures -/



end


