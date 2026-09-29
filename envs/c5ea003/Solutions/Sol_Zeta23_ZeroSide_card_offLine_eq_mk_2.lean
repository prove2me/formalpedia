-- Prove2me | solution 2 for Zeta23.ZeroSide.card_offLine_eq_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-18T04:07:12.258742+00:00
-- url     : https://prove2.me/submissions/3ed761ae-4954-4216-9af4-e9503a1707c8

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
import Theorems.Thm_Zeta23_ZeroSide_ZeroBlockData_sum_split

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



/-- #𝒵(I') = #(𝒮₁∪𝒮₂) + 2p. -/
lemma card_eq_onLine_add : Fintype.card ι = #D.onLine + 2 * P.p := by
  have := D.sum_split P (fun _ => (1 : ℕ))
  simpa [sum_const, smul_eq_mul, PairReps.p, Nat.mul_comm] using this








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



omit Z T in
lemma card_filter_coe (s : Finset ℂ) (p : ℂ → Prop) (q : s → Prop)
    (h : ∀ z : s, q z ↔ p z) : #{z : s | q z} = #(s.filter p) := by
  apply Finset.card_bij (fun (z : s) _ => (z : ℂ))
  · intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz ⊢
    exact ⟨z.2, (h z).mp hz⟩
  · intro a _ b _ hab; exact Subtype.ext hab
  · intro b hb
    simp only [mem_filter] at hb
    exact ⟨⟨b, hb.1⟩, by simp only [mem_filter, mem_univ, true_and]; exact (h _).mpr hb.2, rfl⟩




lemma offLine_eq : Z.offLine T = ↑((ZI Z T).filter (fun ρ => ¬ ρ.re = 1 / 2)) := by
  ext ρ
  simp only [ZeroConfig.offLine, Set.mem_inter_iff, Set.mem_setOf_eq, Finset.coe_filter, mem_ZI, ne_eq]







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
open Zeta23 Classical
variable (Z : ZeroConfig) (T : ℝ)
variable {d : Type*} [Fintype d] [DecidableEq d] (v : ZI Z T → d → ℂ)
    (hv : ∀ z : ZI Z T, v ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (v z))

theorem solution : (Z.offLine T).ncard = 2 * (mkPairReps Z T v hv).p := by
  rw [offLine_eq, Set.ncard_coe_finset]
  have h1 := (mkData Z T v hv).card_eq_onLine_add (mkPairReps Z T v hv)
  have h2 : #((ZI Z T).filter fun ρ => ρ.re = 1 / 2) + #((ZI Z T).filter fun ρ => ¬ ρ.re = 1 / 2)
      = #(ZI Z T) := Finset.card_filter_add_card_filter_not _
  have h3 : #(mkData Z T v hv).onLine = #((ZI Z T).filter fun ρ => ρ.re = 1 / 2) := by
    convert card_filter_coe (ZI Z T) (fun ρ => ρ.re = 1 / 2) (fun z => (mkData Z T v hv).σ z = z)
      (fun z => mkData_σ_eq_iff Z T v hv z) using 2
    ext; simp [ZeroBlockData.onLine]
  have h4 : Fintype.card (ZI Z T) = #(ZI Z T) := Fintype.card_coe _
  omega
