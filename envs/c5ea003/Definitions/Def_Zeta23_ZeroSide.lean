-- Prove2me | Definitions.Def_Zeta23_ZeroSide
-- name    : Zeta23_ZeroSide
-- status  : Definition
-- author  : @Community (Bot)
-- created : 2026-08-17T20:12:30.432776+00:00
-- url     : https://prove2.me/theorems/17534d10-d110-472b-a743-cd5309cfad6d
-- title:
--   Block structure of the zero side ([eq:AE], [prop:block])
-- statement:
--   The zero-side infrastructure of the paper's §4 ("The zero side: signature and rank"): the block structure of the window $\mathcal Z(I')$ of distinct zeros with ordinate $\gamma\in I'$, and the matrices of [eq:AE], formalised $\zeta$-free over abstract data.
--
--   **The abstract data.** `ZeroBlockData` carries: a finite index type $\iota$ of *distinct* points $z$, explicit multiplicities $m\,z\ge1$, evaluation vectors $v\,z=(\hat\varphi(\gamma_z-\tau_k))_{k<d}\in\mathbb C^d$, and the involution $\sigma=(\rho\mapsto1-\bar\rho)$ satisfying $m\circ\sigma=m$ and $v(\sigma z)=\overline{v\,z}$ (fields `m`, `v`, `σ`, with laws `σ_invol`, `m_σ`, `v_σ`).
--
--   **Classification** (the paper's Block structure): `onLine` is $\mathcal S_1\cup\mathcal S_2$, the on-line points, characterised by $\beta=\tfrac12\iff\sigma\rho=\rho$ (`reflect_eq_self_iff`); `S₁` is the simple on-line zeros ($m_\rho=1$), `S₂` the on-line zeros with $m_\rho\ge2$, with cardinalities `s₁`, `s₂`; `PairReps` chooses one representative from each off-line pair $\{\rho,1-\bar\rho\}\in\mathcal P$, with `p` $:=\#\mathcal P$ (at instantiation: the members with $\beta>\tfrac12$, `mkPairReps`). The counts `Ncount` $N(I')=\sum_\rho m_\rho$ [eq:Ncount] and `Non` $N_{\mathrm{on}}(I'):=\sum_{\rho\in\mathcal S_1\cup\mathcal S_2}m_\rho$ realise $\#\mathcal Z(I')=s_1+s_2+2p$ and $N(I')\ge s_1+2s_2+2p$, $N(I')\ge N_{\mathrm{on}}(I')+2p$.
--
--   **The matrices** [eq:AE]: `blockA` is
--   $$A_{kl} := \sum_{\rho:\gamma\in I'} m_\rho\,\hat\varphi(\gamma_\rho-\tau_k)\,\hat\varphi(\gamma_\rho-\tau_l),\quad\text{i.e. } A=\sum_\rho m_\rho\,u_\rho u_\rho^{\mathsf T}$$
--   (transpose, **not** conjugate-transpose), real symmetric because conjugation permutes the summands via $\rho\mapsto1-\bar\rho$ (`blockA_isHermitian`). Its decomposition: the on-line part `onPart` $\sum_{\mathcal S_1\cup\mathcal S_2}m_\rho u_\rho u_\rho^{\mathsf T}$ (positive semidefinite, since $u_\rho$ is real for on-line $\rho$), and the pair parts `rePart` $\sum_{\mathcal P}2m_\rho x_\rho x_\rho^{\mathsf T}$ and `imPart` $\sum_{\mathcal P}2m_\rho y_\rho y_\rho^{\mathsf T}$ with $x_\rho:=\operatorname{Re}u_\rho$, $y_\rho:=\operatorname{Im}u_\rho$. For [prop:block] (ii): `blockP`/`hatP` is $P:=(aL^2)^{-1}\sum_{\mathcal S_1\cup\mathcal S_2}m_\rho u_\rho u_\rho^{\mathsf T}$ and `blockQ`/`hatQ` is $Q:=\hat A-P$, both Hermitian.
--
--   **Instantiation** (Section 3, from `Defs.lean`): `ZI` is $\mathcal Z(I')$ as a `Finset` of $\mathbb C$, `evalVec` the vectors $u_\rho$, `blockData`/`mkData` the block data at $m:=$ `Z.mult`, $\sigma:=\rho\mapsto1-\bar\rho$; reflection facts `gammaOf_reflect` ($\gamma_{1-\bar\rho}=\bar\gamma_\rho$) and `evalVec_reflect` ($u_{1-\bar\rho}=\bar u_\rho$); and the hypothesis shapes `PhiHatConj` ($\overline{\hat\varphi(\bar z)}=\hat\varphi(z)$), `PhiHatReal` ($\hat\varphi$ real on $\mathbb R$), `PoissonSq` (the Poisson-summation identity $\sum_{k\in\mathbb Z}\hat\varphi(\gamma-\tau_k)^2=aL^2$ of [lem:poisson]).
--
--   **Role.** Built on the §3 linear algebra (`RHLinalg`: positive index, subadditivity, Sylvester), this module proves [prop:block] — the signature/rank inequalities that convert the trace bounds into the lower bound for on-line zeros — for an abstract configuration, instantiated at $\zeta$'s zero window and consumed by the assembly of Theorem A.
-- source:
--   https://github.com/anthropics/zeta-23-lean/blob/182afbf851aa42a8ae78507be83f2356d3a33260/Zeta23/ZeroSide.lean, docstring tags [eq:AE], [prop:block]

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

/-- Abstract zero-side data of the window 𝒵(I') [§4 Block structure]: distinct points z : ι with
explicit multiplicity `m z ≥ 1`, evaluation vectors `v z = (φ̂(γ_z − τ_k))_k`, and the involution
`σ = (ρ ↦ 1 − ρ̄)` with `m ∘ σ = m` and `v (σ z) = conj ∘ v z`. -/
structure ZeroBlockData (ι d : Type*) where
  /-- multiplicity m_ρ of the distinct zero ρ -/
  m : ι → ℕ
  one_le_m : ∀ z, 1 ≤ m z
  /-- evaluation vector u_ρ := (φ̂(γ_ρ − τ_k))_{0 ≤ k < d} -/
  v : ι → d → ℂ
  /-- ρ ↦ 1 − ρ̄ on 𝒵(I') -/
  σ : ι → ι
  σ_invol : Function.Involutive σ
  /-- m_{1−ρ̄} = m_ρ -/
  m_σ : ∀ z, m (σ z) = m z
  /-- u_{1−ρ̄} = conj u_ρ -/
  v_σ : ∀ z, v (σ z) = star (v z)

namespace ZeroBlockData

variable (D : ZeroBlockData ι d)

/-- 𝒮₁ ∪ 𝒮₂: on-line points (β = ½ ⟺ fixed by ρ ↦ 1−ρ̄). -/
def onLine : Finset ι := {z | D.σ z = z}

/-- 𝒮₁: on-line and simple (m_ρ = 1). -/
def S₁ : Finset ι := {z | D.σ z = z ∧ D.m z = 1}

/-- 𝒮₂: on-line with m_ρ ≥ 2. -/
def S₂ : Finset ι := {z | D.σ z = z ∧ 2 ≤ D.m z}

/-- s₁ := #𝒮₁ -/
def s₁ : ℕ := #D.S₁

/-- s₂ := #𝒮₂ -/
def s₂ : ℕ := #D.S₂

/-- N(I') = Σ_{ρ ∈ 𝒵(I')} m_ρ (with multiplicity) [eq:Ncount]. -/
def Ncount : ℕ := ∑ z, D.m z

/-- N_on(I') := Σ_{ρ ∈ 𝒮₁ ∪ 𝒮₂} m_ρ. -/
def Non : ℕ := ∑ z ∈ D.onLine, D.m z

/-- A choice of one representative from each off-line pair {ρ, 1−ρ̄} ∈ 𝒫; `p := #R`.
(At instantiation: R = the members with β > ½.) -/
structure PairReps where
  R : Finset ι
  off : ∀ z ∈ R, D.σ z ≠ z
  σ_not_mem : ∀ z ∈ R, D.σ z ∉ R
  cover : ∀ z, D.σ z ≠ z → z ∈ R ∨ D.σ z ∈ R

variable {D}

/-- p := #𝒫, the number of off-line pairs. -/
def PairReps.p (P : D.PairReps) : ℕ := #P.R


variable (D) (P : D.PairReps)

lemma mem_onLine {z : ι} : z ∈ D.onLine ↔ D.σ z = z := by simp [onLine]










/-! ### The matrix A [eq:AE] and its decomposition -/

/-- A_{kl} := Σ_{ρ : γ ∈ I'} m_ρ φ̂(γ_ρ − τ_k) φ̂(γ_ρ − τ_l)  [eq:AE]; i.e. A = Σ_ρ m_ρ u_ρ u_ρᵀ
(transpose, NOT conjugate-transpose). -/
def blockA : Matrix d d ℂ := ∑ z, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)


/-- u_ρ is a real vector for ρ on the line. -/
lemma star_v_of_onLine {z : ι} (hz : D.σ z = z) : star (D.v z) = D.v z := by
  rw [← D.v_σ, hz]

/-- "A is real symmetric (same argument as for G: conjugation permutes the summands via ρ ↦ 1−ρ̄)". -/
theorem blockA_isHermitian : D.blockA.IsHermitian := by
  unfold blockA Matrix.IsHermitian
  rw [conjTranspose_sum]
  simp_rw [conjTranspose_smul, conjTranspose_vecMulVec, ← D.v_σ]
  simp only [star_natCast]
  exact Fintype.sum_equiv D.σ_invol.toPerm _ _ fun z => by simp [D.m_σ]



/-- real part vector x_ρ := Re u_ρ (as a complex vector) -/
def xv (z : ι) : d → ℂ := fun k => ((D.v z k).re : ℂ)
/-- imaginary part vector y_ρ := Im u_ρ (as a complex vector) -/
def yv (z : ι) : d → ℂ := fun k => ((D.v z k).im : ℂ)



/-- the on-line part Σ_{ρ∈𝒮₁∪𝒮₂} m_ρ u_ρ u_ρᵀ -/
def onPart : Matrix d d ℂ := ∑ z ∈ D.onLine, (D.m z : ℂ) • vecMulVec (D.v z) (D.v z)
/-- Σ_𝒫 2m_ρ x_ρ x_ρᵀ -/
def rePart : Matrix d d ℂ := ∑ z ∈ P.R, ((2 * D.m z : ℝ) : ℂ) • vecMulVec (D.xv z) (D.xv z)
/-- Σ_𝒫 2m_ρ y_ρ y_ρᵀ -/
def imPart : Matrix d d ℂ := ∑ z ∈ P.R, ((2 * D.m z : ℝ) : ℂ) • vecMulVec (D.yv z) (D.yv z)


omit [DecidableEq d] in
/-- c • x xᵀ ⪰ 0 for a real vector x and real c ≥ 0. -/
lemma posSemidef_smul_vecMulVec {x : d → ℂ} (hx : star x = x) {c : ℝ} (hc : 0 ≤ c) :
    ((c : ℂ) • vecMulVec x x).PosSemidef := by
  have h := posSemidef_vecMulVec_self_star x
  rw [hx] at h
  exact h.smul (Complex.zero_le_real.mpr hc)

lemma onPart_posSemidef : D.onPart.PosSemidef := by
  unfold onPart
  refine posSemidef_sum _ fun z hz => ?_
  have := posSemidef_smul_vecMulVec (D.star_v_of_onLine ((D.mem_onLine).mp hz)) (Nat.cast_nonneg (D.m z))
  simpa using this










/-! ### prop:block (ii): Â = P + Q in the units [eq:hatunits] -/

/-- P := (aL²)⁻¹ Σ_{ρ ∈ 𝒮₁∪𝒮₂} m_ρ u_ρ u_ρᵀ  [prop:block proof of (ii)], with c := aL². -/
def blockP (c : ℝ) : Matrix d d ℂ := ((c⁻¹ : ℝ) : ℂ) • D.onPart

/-- Q := Â − P, "the sum of the pair contributions". -/
def blockQ (c : ℝ) : Matrix d d ℂ := ((c⁻¹ : ℝ) : ℂ) • (D.blockA - D.onPart)








omit [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d] in
lemma isHermitian_real_smul {A : Matrix d d ℂ} (hA : A.IsHermitian) (r : ℝ) :
    ((r : ℂ) • A).IsHermitian :=
  hA.smul (by rw [IsSelfAdjoint, Complex.star_def, Complex.conj_ofReal])

/-- Q is Hermitian (real symmetric). -/
theorem blockQ_isHermitian (c : ℝ) : (D.blockQ c).IsHermitian :=
  isHermitian_real_smul (D.blockA_isHermitian.sub D.onPart_posSemidef.isHermitian) _



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

lemma ZIprime_finite : (Z.ZIprime T).Finite := Z.finite_window _ _

/-- 𝒵(I') as a Finset of ℂ. -/
def ZI : Finset ℂ := (ZIprime_finite Z T).toFinset

lemma mem_ZI {ρ : ℂ} : ρ ∈ ZI Z T ↔ ρ ∈ Z.ZIprime T := Set.Finite.mem_toFinset _


lemma mem_ZIprime_iff {ρ : ℂ} :
    ρ ∈ Z.ZIprime T ↔ ρ ∈ Z.carrier ∧ T - D0 T < ρ.im ∧ ρ.im ≤ 2 * T + D0 T := by
  simp [ZeroConfig.ZIprime, ZeroConfig.window]

omit Z T in
lemma reflect_reflect (ρ : ℂ) : reflect (reflect ρ) = ρ := by simp [reflect]
omit Z T in
lemma reflect_re (ρ : ℂ) : (reflect ρ).re = 1 - ρ.re := by simp [reflect]
omit Z T in
lemma reflect_im (ρ : ℂ) : (reflect ρ).im = ρ.im := by simp [reflect]

omit Z T in
/-- fixed points of ρ ↦ 1 − ρ̄ are exactly the points with β = 1/2 -/
lemma reflect_eq_self_iff (ρ : ℂ) : reflect ρ = ρ ↔ ρ.re = 1 / 2 := by
  constructor
  · intro h; have := congrArg Complex.re h; rw [reflect_re] at this; linarith
  · intro h
    apply Complex.ext
    · rw [reflect_re, h]; norm_num
    · rw [reflect_im]

omit Z T in
/-- γ_{1−ρ̄} = conj γ_ρ. -/
lemma gammaOf_reflect (ρ : ℂ) : gammaOf (reflect ρ) = starRingEnd ℂ (gammaOf ρ) := by
  simp only [gammaOf, reflect, map_div₀, map_sub, map_one, map_ofNat, Complex.conj_I]
  field_simp
  ring


lemma reflect_mem_ZI {ρ : ℂ} (h : ρ ∈ ZI Z T) : reflect ρ ∈ ZI Z T := by
  rw [mem_ZI, mem_ZIprime_iff] at h ⊢
  exact ⟨Z.reflect_mem ρ h.1, by rw [reflect_im]; exact h.2⟩

lemma mem_carrier_of_mem_ZI {ρ : ℂ} (h : ρ ∈ ZI Z T) : ρ ∈ Z.carrier :=
  ((mem_ZIprime_iff Z T).mp ((mem_ZI Z T).mp h)).1

/-- Block data of 𝒵(I') with an arbitrary σ-equivariant family of vectors v (the counting facts do
not depend on v; the matrix facts use v ρ = (φ̂(γ_ρ − τ_k))_k). -/
def mkData {d : Type*} (v : ZI Z T → d → ℂ)
    (hv : ∀ z : ZI Z T, v ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (v z)) :
    ZeroBlockData (ZI Z T) d where
  m z := Z.mult z
  one_le_m z := Z.one_le_mult _ (mem_carrier_of_mem_ZI Z T z.2)
  v := v
  σ z := ⟨reflect z, reflect_mem_ZI Z T z.2⟩
  σ_invol _ := Subtype.ext (reflect_reflect _)
  m_σ z := Z.mult_reflect _ (mem_carrier_of_mem_ZI Z T z.2)
  v_σ := hv

section mk
variable {d : Type*} [Fintype d] [DecidableEq d] (v : ZI Z T → d → ℂ)
    (hv : ∀ z : ZI Z T, v ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (v z))

@[simp] lemma mkData_σ (z : ZI Z T) : ((mkData Z T v hv).σ z : ℂ) = reflect z := rfl

lemma mkData_σ_eq_iff (z : ZI Z T) : (mkData Z T v hv).σ z = z ↔ (z : ℂ).re = 1 / 2 := by
  rw [Subtype.ext_iff, mkData_σ, reflect_eq_self_iff]

/-- Canonical representatives of the off-line pairs: the member with β > 1/2. -/
def mkPairReps : (mkData Z T v hv).PairReps where
  R := {z | 1 / 2 < (z : ℂ).re}
  off z hz h := by
    rw [mkData_σ_eq_iff] at h
    simp only [mem_filter, mem_univ, true_and] at hz
    linarith
  σ_not_mem z hz h := by
    simp only [mem_filter, mem_univ, true_and, mkData_σ, reflect_re] at hz h
    linarith
  cover z hz := by
    rw [ne_eq, mkData_σ_eq_iff] at hz
    simp only [mem_filter, mem_univ, true_and, mkData_σ, reflect_re]
    rcases lt_or_gt_of_ne hz with h | h
    · right; linarith
    · left; exact h












end mk

/-- the zero family of vectors (for the v-independent counting statements) -/
def zeroVec : ZI Z T → Unit → ℂ := fun _ _ => 0






/-! ### The matrix A = Z.Az P T and prop:block for Ã := P.tilde T A, Â := P.hat T A -/

variable (P : Params)

/-- Hypothesis shape: conj φ̂(z̄) = φ̂(z) [subsec:family after eq:fk]; = Params.phiHat_conj (Taper.lean). -/
abbrev PhiHatConj : Prop := ∀ z : ℂ, P.phiHat T (starRingEnd ℂ z) = starRingEnd ℂ (P.phiHat T z)
/-- Hypothesis shape: φ̂ is real on ℝ; = Params.phiHat_ofReal (Taper.lean). -/
abbrev PhiHatReal : Prop := ∀ r : ℝ, P.phiHat T r = (P.phiHatR T r : ℂ)
/-- Hypothesis shape: lem:poisson "in particular Σ_{k∈ℤ} φ̂(γ−τ_k)² = aL²" for real γ;
= Params.hasSum_phiHatR_sq (Poisson.lean). -/
abbrev PoissonSq : Prop :=
  ∀ γ : ℝ, HasSum (fun k : ℤ => P.phiHatR T (γ - P.tau T k) ^ 2) (P.a T * P.L T ^ 2)

/-- the evaluation vectors u_ρ := (φ̂(γ_ρ − τ_k))_{0≤k<d}  [prop:block proof] -/
def evalVec : ZI Z T → Fin (P.d T) → ℂ := fun z k => P.phiHat T (gammaOf z - P.tau T k)

variable {Z T P}

/-- u_{1−ρ̄} = conj u_ρ (from γ_{1−ρ̄} = conj γ_ρ, τ_k ∈ ℝ, φ̂(conj w) = conj φ̂(w)). -/
lemma evalVec_reflect (hconj : PhiHatConj T P) :
    ∀ z : ZI Z T, evalVec Z T P ⟨reflect z, reflect_mem_ZI Z T z.2⟩ = star (evalVec Z T P z) := by
  intro z
  funext k
  simp only [evalVec, Pi.star_apply, RCLike.star_def]
  rw [gammaOf_reflect, ← hconj, map_sub, Complex.conj_ofReal]

variable (Z T P)

/-- The block data of 𝒵(I') [eq:AE]: m := Z.mult, u_ρ := (φ̂(γ_ρ − τ_k))_{0≤k<d}, σ := ρ ↦ 1 − ρ̄. -/
def blockData (hconj : PhiHatConj T P) : ZeroBlockData (ZI Z T) (Fin (P.d T)) :=
  mkData Z T (evalVec Z T P) (evalVec_reflect hconj)










/-- P of prop:block (ii): (aL²)⁻¹ Σ_{ρ∈𝒮₁∪𝒮₂} m_ρ u_ρ u_ρᵀ. -/
def hatP (hconj : PhiHatConj T P) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  (blockData Z T P hconj).blockP (P.a T * P.L T ^ 2)

/-- Q of prop:block (ii): Â − P ("the sum of the pair contributions"). -/
def hatQ (hconj : PhiHatConj T P) : Matrix (Fin (P.d T)) (Fin (P.d T)) ℂ :=
  (blockData Z T P hconj).blockQ (P.a T * P.L T ^ 2)










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


