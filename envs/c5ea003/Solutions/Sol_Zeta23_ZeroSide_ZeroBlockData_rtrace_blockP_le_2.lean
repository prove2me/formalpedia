-- Prove2me | solution 2 for Zeta23.ZeroSide.ZeroBlockData.rtrace_blockP_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:08:06.650259+00:00
-- url     : https://prove2.me/submissions/cd843ecb-6e2f-4fd2-8a0c-379b8257986c

import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_Hypotheses
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_ZeroSide
import Theorems.Thm_Zeta23_ZeroSide_ZeroBlockData_rtrace_onPart

-- from Zeta23.ZeroSide
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/ZeroSide.lean — paper §4 "The zero side: signature and rank", Block structure + prop:block.
Builds on the §3 formalization (Zeta23.LinAlg, namespace RHLinalg): posIndex, posIndex_add_le
(subadditivity, the corollary of lem:inertia), Sylvester's subspace characterization,
posIndex_eq_rank_of_posSemidef.

Reference text: the paper, labels [eq:AE], [eq:Ncount], [eq:hatunits], [prop:block].

Design: this file is ζ-free. Section 1 is generic Hermitian-matrix
lemmas missing from Mathlib/RHLinalg. Section 2 proves prop:block for an ABSTRACT finite
zero configuration `ZeroBlockData` (distinct points z with explicit multiplicities m z ≥ 1,
the involution σ = (ρ ↦ 1 − conj ρ) with m ∘ σ = m, and evaluation vectors v z = (φ̂(γ_z − τ_k))_k with
v (σ z) = conj ∘ v z). Section 3 instantiates from Defs.lean's ZeroConfig, φ̂, τ_k, a, L and
lem:poisson.
-/

noncomputable section

set_option linter.unusedSectionVars false

open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators

namespace Zeta23.ZeroSide

/-! ## Section 1. Generic lemmas on rank and positive index -/

section Generic

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]











end Generic

/-! ## Section 2. The abstract block structure (paper §4: [eq:AE], Block structure, [eq:Ncount], [prop:block])

Paper §4, Block structure, verbatim: "Let 𝒵(I') be the set of distinct zeros with γ ∈ I'. Classify its
points as follows: 𝒮₁: β = ½ and m_ρ = 1 (simple zeros on the line); s₁ := #𝒮₁; 𝒮₂: β = ½ and
m_ρ ≥ 2; s₂ := #𝒮₂; 𝒫: unordered pairs {ρ, 1−ρ̄} with β ≠ ½ (both members lie in 𝒵(I'), they are
distinct points, and m_{1−ρ̄} = m_ρ); p := #𝒫. Thus #𝒵(I') = s₁+s₂+2p and, counting with
multiplicity, N(I') = Σ_{𝒮₁} 1 + Σ_{𝒮₂} m_ρ + Σ_{𝒫} 2m_ρ ≥ s₁+2s₂+2p. [eq:Ncount]
Write N_on(I') := Σ_{ρ∈𝒮₁∪𝒮₂} m_ρ, so that also N(I') ≥ N_on(I') + 2p."

We encode 𝒵(I') as a finite index type ι, the grid {0,…,d−1} as a finite type d, and carry:
multiplicities m (≥ 1, explicit — zeros are DISTINCT points), the involution σ = (ρ ↦ 1−ρ̄)
restricted to 𝒵(I') (it preserves the ordinate, hence 𝒵(I')), and the evaluation vectors
u_ρ = (φ̂(γ_ρ − τ_k))_{k<d} ∈ ℂ^d with u_{1−ρ̄} = conj u_ρ (from γ_{1−ρ̄} = conj γ_ρ, τ_k ∈ ℝ, and
conj φ̂(z̄) = φ̂(z) [subsec:family after eq:fk]). On-line ⟺ β = ½ ⟺ σ ρ = ρ.
-/

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]


namespace ZeroBlockData

variable (D : ZeroBlockData ι d)









variable {D}



variable (D) (P : D.PairReps)











/-! ### The matrix A [eq:AE] and its decomposition -/























/-! ### prop:block (ii): Â = P + Q in the units [eq:hatunits] -/














end ZeroBlockData

end Block

/-! ## Section 3. Instantiation against Zeta23.Defs: 𝒵(I') ⊂ ZeroConfig, A = Z.Az P T  [eq:AE]

Here ι := 𝒵(I') = Z.ZIprime T (finite by ZeroConfig.finite_window), d := Fin (P.d T),
m := Z.mult, σ := reflect = (ρ ↦ 1 − conj ρ), v ρ k := φ̂(γ_ρ − τ_k) with γ_ρ = gammaOf ρ, τ_k = P.tau T k.
The analytic inputs are explicit hypotheses of this section (discharged elsewhere in the
repository from Zeta23.Taper / Zeta23.Poisson: Params.phiHat_conj, Params.phiHat_ofReal,
Params.hasSum_phiHatR_sq):
  hconj : ∀ z, φ̂(conj z) = conj φ̂(z)                       [subsec:family, after eq:fk]
  hreal : ∀ r : ℝ, φ̂(r) = φ̂_ℝ(r) (φ̂ real on ℝ)
  hPois : ∀ γ : ℝ, HasSum (k ↦ φ̂(γ − τ_k)²) (aL²)            [lem:poisson, "in particular"]
-/

section Inst

open Zeta23 Classical

variable (Z : ZeroConfig) (T : ℝ)













section mk
variable {d : Type*} [Fintype d] [DecidableEq d] (v : ZI Z T → d → ℂ)
    (hv : ∀ z : ZI Z T, v ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (v z))

@[simp] lemma mkData_m (z : ZI Z T) : (mkData Z T v hv).m z = Z.mult z := rfl
@[simp] lemma mkData_v : (mkData Z T v hv).v = v := rfl














end mk







/-! ### The matrix A = Z.Az P T and prop:block for Ã := P.tilde T A, Â := P.hat T A -/

variable (P : Params)



variable {Z T P}


variable (Z T P)






















end Inst

/-! ## Section 4. Packaging for Assembly: `Zeta23.Assembly.BlockInputs` -/

section Package

open Zeta23


/-! ### The export for Main.lean: eventually-in-T form with only the genuinely external inputs left

hconj / hreal are discharged here from Zeta23.GzGp.phiHat_conj / phiHat_ofReal
(φ real and even); 0 < L eventually since L = λ·log(T/2π) → ∞. What remains as hypotheses, both in
∀ᶠ form: positivity of a [eq:abdef] (Main has it from Taper: 1 − 2w/L ≤ b ≤ a) and lem:poisson
(Zeta23.Poisson: Params.hasSum_phiHatR_sq). Zeta23/ZeroSide/Final.lean discharges those two as well. -/



end Package

end Zeta23.ZeroSide
end
set_option linter.unusedSectionVars false
open Matrix Finset RHLinalg
open scoped ComplexOrder BigOperators
open Zeta23
open Zeta23.ZeroSide
variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
open ZeroBlockData
variable (D : ZeroBlockData ι d)
variable {D}
variable (D) (P : D.PairReps)

theorem solution {c : ℝ} (hc : 0 < c)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) :
    rtrace (D.blockP c) ≤ (D.Non : ℝ) := by
  have htr : rtrace (D.blockP c) = c⁻¹ * rtrace D.onPart := by
    simp only [rtrace, blockP, trace_smul, smul_eq_mul, RCLike.re_to_complex, Complex.re_ofReal_mul]
  unfold Non
  rw [htr, rtrace_onPart, mul_sum, Nat.cast_sum]
  refine sum_le_sum fun z hz => ?_
  rw [← mul_assoc, mul_comm (c⁻¹), mul_assoc]
  have hm : (0 : ℝ) ≤ D.m z := Nat.cast_nonneg _
  calc (D.m z : ℝ) * (c⁻¹ * ∑ k, ‖D.v z k‖ ^ 2) ≤ D.m z * (c⁻¹ * c) := by
        gcongr; exact hPois z hz
    _ = D.m z := by rw [inv_mul_cancel₀ hc.ne', mul_one]
