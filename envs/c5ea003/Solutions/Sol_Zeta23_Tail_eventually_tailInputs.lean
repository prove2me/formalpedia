-- Prove2me | solution 1 for Zeta23.Tail.eventually_tailInputs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-08-17T23:51:37.986673+00:00
-- url     : https://prove2.me/submissions/e259279a-bbcc-4813-975a-b4b9b0ec61ff

import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Finprod
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Rearrangement
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Set.Card
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Instances.Matrix
import Definitions.Def_Zeta23_Assembly_Inputs
import Definitions.Def_Zeta23_Defs
import Definitions.Def_Zeta23_LinAlg_HermitianPosPart
import Definitions.Def_Zeta23_LinAlg_PosIndex
import Definitions.Def_Zeta23_LinAlg_Sylvester
import Definitions.Def_Zeta23_LinAlg_VonNeumann
import Definitions.Def_Zeta23_Tail
import Definitions.Def_Zeta23_Tail_Basic
import Definitions.Def_Zeta23_Tail_RankOne
import Theorems.Thm_Zeta23_Tail_TailHyp_Ez_isHermitian
import Theorems.Thm_Zeta23_Tail_prop_tail

-- from Zeta23.LinAlg.PosIndex
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
The linear algebra of §3 of the paper (Hermitian positive/negative parts, inertia, the positive index,
von Neumann's trace inequality, the rank–trace inequality, Weyl's perturbation bound). These seven files
were written first as a self-contained development (namespace `RHLinalg`) accompanying §3 of the paper, by the
paper's authors, and are incorporated here unchanged; they have no upstream outside this project (see README
§ Provenance and attribution).
-/

/-!
# Positive index of a Hermitian matrix

For a Hermitian matrix `A` over `𝕜 = ℝ` or `ℂ`, the *positive index*
`n₊(A)` is the number of strictly positive eigenvalues. By Sylvester's law
of inertia this equals the maximal dimension of a subspace on which the
Hermitian form `x ↦ xᴴ A x` is positive definite.

This file defines `posIndex` via the eigenvalue count, together with the
real-valued trace `rtrace` and squared Frobenius norm `frobSq` needed for
the rank–trace inequality (paper §3, `lem:ranktrace`).
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace RHLinalg

variable {𝕜 : Type*} [RCLike 𝕜]
variable {n : Type*} [Fintype n] [DecidableEq n]








lemma rtrace_eq_sum_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    rtrace A = ∑ i, hA.eigenvalues i := by
  unfold rtrace
  rw [hA.trace_eq_sum_eigenvalues]
  simp

section Reindex

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)





end Reindex

open Unitary in
/-- For a Hermitian matrix, `‖A‖_F² = ∑ᵢ λᵢ²` (sum of squared eigenvalues). -/
lemma frobSq_hermitian_eq_sum_sq_eigenvalues {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    frobSq A = ∑ i, (hA.eigenvalues i) ^ 2 := by
  -- A = U D Uᴴ ⟹ AᴴA = A² = U D² Uᴴ ⟹ tr(AᴴA) = ∑ λᵢ²
  unfold frobSq
  rw [hA.eq]
  conv_lhs => rw [hA.spectral_theorem, ← map_mul, conjStarAlgAut_apply,
    trace_mul_cycle, coe_star_mul_self, one_mul,
    diagonal_mul_diagonal, trace_diagonal]
  simp [sq]

end RHLinalg
end
end

-- from Zeta23.Tail.Count
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/Count.lean — the zero-count sum in the proof of [prop:tail] (the paper §4.2).


Paper, verbatim: "It remains to bound ∑_{γ∉I'} m_ρ D⁻³ (zeros counted with multiplicity).
Zeros with γ > 2T+D₀: grouping them into γ ∈ (2T+D₀+j, 2T+D₀+j+1], j ≥ 0, this part is at
most ∑_{j≥0} A₀ log(2T+D₀+j+4)(D₀+j)⁻³ ≤ (3/2)A₀ log(4T) D₀⁻² for T large (split at j = T
and use D₀ ≥ 2). Zeros with 0 < γ < T−D₀ contribute likewise at most (3/2)A₀ log(4T)D₀⁻²,
and zeros with γ ≤ 0 have D ≥ T and contribute at most ∑_{j≥0} A₀ log(j+4)(T+j)⁻³
≪ T⁻² log T. Altogether ∑_{γ∉I'} m_ρ D⁻³ ≤ 4A₀ log(4T) D₀⁻² for T ≥ T₀."

We prove the bound for every FINITE sub-family of tail zeros (which yields both the
summability and the bound for the full series downstream), with the explicit absolute
threshold T₀ of Zeta23/Tail/Basic.lean. Only the final constant 4 is load-bearing (it is
the 4 in θ₀); we do not follow the paper's intermediate 3/2 + 3/2 + o(1) split. Our
grouping: unit windows indexed by the integer distance j from the nearer endpoint of
I = [T,2T] (lower side: T−j−1 < γ ≤ T−j, which also covers ALL γ ≤ 0; upper side:
2T+j < γ ≤ 2T+j+1), each window weighted by max(D₀, j)⁻³ and counted by the two-sided
local count ≤ A₀ log(2T+4+j); integrals are replaced by telescoping sums.
-/

noncomputable section

open Finset Real

namespace Zeta23
namespace Tail

/-! #### Telescoping sums replacing ∫ x⁻³ and ∫ x⁻² -/








/-! #### Summing the window weights -/


/-! #### One side of the tail, abstractly -/


/-! #### Numerics at T ≥ T₀ -/

lemma one_le_log_four_mul {T : ℝ} (hT : T₀ ≤ T) : 1 ≤ Real.log (4 * T) := by
  have hT' : (300 : ℝ) ≤ T := hT
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith


/-! #### The zero-count sum -/


/-! #### The boundary count N(I' ∖ I) -/



end Tail
end Zeta23
end
end

-- from Zeta23.Tail.RankOne
section
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail/RankOne.lean — the linear-algebra step of [prop:tail] (the paper §4.2):
eigenvalue bounds for a (possibly infinite) sum of rank-one matrices m_ρ u_ρ u_ρᵀ.


Paper, verbatim (proof of [prop:tail]): "Since E = ∑_{γ∉I'} m_ρ u_ρ u_ρᵀ and
‖uuᵀ‖ = ‖u‖₂², ‖E‖ ≤ ∑_{γ∉I'} m_ρ ‖u_ρ‖₂²  [eq:Enormsum]" … "The trace-norm bound follows
from the same chain, since ‖uuᵀ‖₁ = ‖u‖₂² as well".

Design (avoiding Schatten-norm machinery): the trace norm of a Hermitian
matrix is DEFINED here as traceNorm hE := ∑ᵢ |λᵢ(E)|, and the operator-norm bound is
delivered in the shape RHLinalg.weyl_posIndexAbove_le consumes, namely ∀ i, |λᵢ(E)| ≤ θ.
Both follow from one inequality, traceNorm hE ≤ ∑_ρ c_ρ ‖u_ρ‖₂², proved directly in the
eigenbasis: λᵢ = vᵢ* E vᵢ = ∑_ρ c_ρ ⟨vᵢ,u_ρ⟩⟨v̄ᵢ,u_ρ⟩, |⟨vᵢ,u_ρ⟩⟨v̄ᵢ,u_ρ⟩| ≤ (|⟨vᵢ,u_ρ⟩|² +
|⟨vᵢ,ū_ρ⟩|²)/2, and Parseval ∑ᵢ|⟨vᵢ,w⟩|² = ‖w‖² for the unitary eigenvector matrix.
NOTE u_ρ u_ρᵀ (Matrix.vecMulVec u u), NOT u_ρ u_ρ*: the u_ρ = (φ̂(γ_ρ − τ_k))_k are complex
for off-line zeros and the paper's E is complex-symmetric termwise; Hermitian-ness of the
total (from the ρ ↦ 1−ρ̄ symmetry) is taken as the hypothesis hE.
-/

noncomputable section

open Matrix Finset
open scoped ComplexOrder

namespace Zeta23
namespace Tail

open RHLinalg

variable {n : Type*} [Fintype n] [DecidableEq n]



lemma traceNorm_nonneg {E : Matrix n n ℂ} (hE : E.IsHermitian) : 0 ≤ traceNorm hE :=
  sum_nonneg fun _ _ => abs_nonneg _

/-- |tr E| ≤ ‖E‖₁ (used in [prop:zeroside-rank]: "|tr Ê| ≤ ‖Ê‖₁"). -/
lemma abs_rtrace_le_traceNorm {E : Matrix n n ℂ} (hE : E.IsHermitian) :
    |rtrace E| ≤ traceNorm hE := by
  rw [rtrace_eq_sum_eigenvalues hE]
  exact abs_sum_le_sum_abs _ _

/-- ‖E‖_F² ≤ ‖E‖₁² (used in [prop:zeroside-rank]: "‖Â‖_F ≤ ‖Ĝ‖_F + ‖Ê‖_F ≤ ‖Ĝ‖_F + ‖Ê‖₁"). -/
lemma frobSq_le_traceNorm_sq {E : Matrix n n ℂ} (hE : E.IsHermitian) :
    frobSq E ≤ (traceNorm hE) ^ 2 := by
  rw [frobSq_hermitian_eq_sum_sq_eigenvalues hE, traceNorm]
  calc ∑ i, hE.eigenvalues i ^ 2 = ∑ i, |hE.eigenvalues i| ^ 2 := by simp [sq_abs]
    _ ≤ (∑ i, |hE.eigenvalues i|) ^ 2 :=
      sum_sq_le_sq_sum_of_nonneg (fun i _ => abs_nonneg _)





end Tail
end Zeta23
end
end

-- from Zeta23.Tail
/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Zeta23/Tail.lean — Proposition [prop:tail] (the paper §4.2 "The tail"), assembled for the
concrete objects of Zeta23/Defs.lean.

Paper, verbatim: "Proposition [prop:tail]. Let A₀ ≥ 1 be an absolute constant such that
N(t+1)−N(t) ≤ A₀ log(t+3) for all t ≥ 0. Then for T ≥ T₀,
  ‖Ẽ‖ ≤ θ₀ := 4A₀ C₁² X^{1/2} log(4T)/D₀²,   C₁ := ‖φ″‖₁ = 2‖ϱ″‖₁/w,
so that θ₀ ≤ 32A₀‖ϱ″‖₁² l T^{λ/2−1} ≪ l T^{λ/2−1}. Moreover the trace norm satisfies
‖Ê‖₁ ≤ θ₀/(aL) ≤ 2θ₀/L."
Here E := G − A [eq:AE] is the contribution of the zeros with ordinate γ ∉ I' := (T−D₀, 2T+D₀],
D₀ := T^{1/2} [eq:D0] (including all zeros with γ ≤ 0), Ẽ := E/L,
Ê := E/(aL²) [eq:hatunits].

Structure of the proof (sub-files):
* Zeta23/Tail/RankOne.lean — ‖E‖, ‖E‖₁ ≤ ∑ m_ρ ‖u_ρ‖₂² for E = ∑ m_ρ u_ρ u_ρᵀ  [eq:Enormsum];
* Zeta23/Tail/Grid.lean    — ∑_{k<d} |γ−τ_k|⁻⁴ ≤ L·dist(γ,I)⁻³;
* Zeta23/Tail/Count.lean   — ∑_{γ∉I'} m_ρ dist(γ,I)⁻³ ≤ 4A₀ log(4T)/T, and N(I'∖I) ≪ D₀ l;
* this file              — [eq:hfbound] ⇒ ‖u_ρ k‖ ≤ e^{L/4}C₁|γ−τ_k|⁻², summability of the
  zero-side series entrywise, E = (the series over γ ∉ I'), and the two bounds in the exact
  shapes consumed downstream: ∀ i, |λᵢ(Ẽ)| ≤ θ₀ (for RHLinalg.weyl_posIndexAbove_le) and
  traceNorm Ê ≤ θ₀/(aL) (for [prop:zeroside-rank]).

Hypotheses taken (all proved elsewhere in the repository; none are Lean axioms):
* hloc  — PaperInputs.RvM.local (Hypotheses.lean), two-sided unit-window form;
* hdecay — [eq:hfbound] specialised to f = φ, in the exact shape of
  Zeta23.Params.norm_phiHat_sub_I_mul_le (Taper.lean), with C₁ := P.C1 T = ‖φ″‖₁;
* hEt/hEh — Hermitian-ness of Ẽ, Ê (from the ρ ↦ 1−ρ̄ symmetry).
-/

noncomputable section

open Matrix Finset Complex
open scoped ComplexOrder

namespace Zeta23
namespace Tail

open RHLinalg

/-! ### θ₀ and its size -/


lemma theta0_nonneg {A₀ K T : ℝ} (hA₀ : 0 ≤ A₀) (hT : T₀ ≤ T) : 0 ≤ theta0 A₀ K T := by
  have hT' : (300:ℝ) ≤ T := hT
  have := one_le_log_four_mul hT
  unfold theta0; positivity



/-! ### The local count from PaperInputs.RvM.local -/


/-! ### The vectors u_ρ and their decay from [eq:hfbound] -/

section Concrete

variable (Z : ZeroConfig) (P : Params) (T : ℝ)




variable {P T}




variable {Z}



end Concrete

/-! ### Summability of the zero-side series and E as the series over γ ∉ I' -/

section Series

variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}



namespace TailHyp

variable (H : TailHyp Z P T A₀ C₁)
include H

lemma A₀_nonneg : 0 ≤ A₀ := by linarith [H.hA₀]












end TailHyp

/-! ### Proposition [prop:tail] -/


end Series

/-! ### E is Hermitian (real symmetric) — "since ρ and 1−ρ̄ have the same ordinate, both index
sets are invariant under ρ ↦ 1−ρ̄, so A and E are real symmetric" [eq:AE] -/

section Hermitian




variable {P : Params} {T : ℝ}


variable {Z : ZeroConfig} {A₀ C₁ : ℝ}


/-- Real scalings of a Hermitian matrix are Hermitian (for Ẽ = E/L, Ê = E/(aL²)). -/
lemma isHermitian_real_smul {n : Type*} {M : Matrix n n ℂ} (hM : M.IsHermitian) (c : ℝ) :
    ((c : ℂ) • M).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [conjTranspose_smul, hM.eq]
  simp [Complex.conj_ofReal]

lemma TailHyp.tilde_Ez_isHermitian (H : TailHyp Z P T A₀ C₁)
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    (P.tilde T (Z.Ez P T)).IsHermitian := by
  have h := isHermitian_real_smul (H.Ez_isHermitian hconj) (P.L T)⁻¹
  unfold Params.tilde; rw [← Complex.ofReal_inv]; exact h

lemma TailHyp.hat_Ez_isHermitian (H : TailHyp Z P T A₀ C₁)
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    (P.hat T (Z.Ez P T)).IsHermitian := by
  have h := isHermitian_real_smul (H.Ez_isHermitian hconj) (P.a T * P.L T ^ 2)⁻¹
  unfold Params.hat
  have e : ((P.a T * P.L T ^ 2)⁻¹ : ℂ) = (((P.a T * P.L T ^ 2)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
  rw [e]; exact h

end Hermitian

/-! ### Exports in the shapes consumed by Zeta23/Assembly.lean (Assembly.TailInputs) -/

section Export

open Filter

variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}

/-- [prop:tail] packaged as Assembly.TailInputs at height T, with
θ₀ = theta0 A₀ (e^{L/4} C₁) T and B := ‖Ê‖₁ = traceNorm Ê. -/
theorem TailHyp.tailInputs (H : TailHyp Z P T A₀ C₁) (ha : 0 < P.a T)
    (hconj : ∀ z : ℂ, P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    Assembly.TailInputs Z P T (theta0 A₀ (Real.exp (P.L T / 4) * C₁) T) := by
  have hEt := H.tilde_Ez_isHermitian hconj
  have hEh := H.hat_Ez_isHermitian hconj
  have hp := prop_tail H ha hEt hEh
  exact
    { theta_nonneg := theta0_nonneg H.A₀_nonneg H.hT
      tilde := ⟨hEt, hp.1⟩
      hat := ⟨traceNorm hEh, traceNorm_nonneg _, abs_rtrace_le_traceNorm _,
        frobSq_le_traceNorm_sq _, hp.2.2⟩ }


/-- L = λ log(T/2π) → ∞; in particular eventually L ≥ 2 (and ≥ 8w, etc.). -/
lemma tendsto_L_atTop (P : Params) (hP : P.Valid) : Tendsto (fun T => P.L T) atTop atTop := by
  unfold Params.L l
  apply Tendsto.const_mul_atTop hP.lam_pos
  exact Real.tendsto_log_atTop.comp (tendsto_id.atTop_div_const (by positivity))




end Export

end Tail
end Zeta23
end
open Matrix Finset Complex
open scoped ComplexOrder
open Zeta23
open Tail
open RHLinalg
open Filter
variable {Z : ZeroConfig} {P : Params} {T A₀ C₁ : ℝ}

theorem solution (Z : ZeroConfig) (P : Params) (hP : P.Valid) {A₀ : ℝ}
    (hA₀ : 1 ≤ A₀) (hloc : ∀ t : ℝ, (Z.N t (t + 1) : ℝ) ≤ A₀ * Real.log (|t| + 3))
    (C₁ : ℝ → ℝ) (hC₁ : ∀ T, 0 ≤ C₁ T)
    (hdecay : ∀ᶠ T in atTop, ∀ (r y : ℝ), |y| ≤ 1 / 2 → (r : ℂ) - I * y ≠ 0 →
      ‖P.phiHat T (r - I * y)‖ ≤ Real.exp (P.L T / 4) * C₁ T / ‖(r : ℂ) - I * y‖ ^ 2)
    (ha : ∀ᶠ T in atTop, 0 < P.a T)
    (hconj : ∀ᶠ T in atTop, ∀ z : ℂ,
      P.phiHat T ((starRingEnd ℂ) z) = (starRingEnd ℂ) (P.phiHat T z)) :
    ∀ᶠ T in atTop, Assembly.TailInputs Z P T (theta0 A₀ (Real.exp (P.L T / 4) * C₁ T) T) := by
  have hL2 : ∀ᶠ T in atTop, 2 ≤ P.L T := (tendsto_L_atTop P hP).eventually_ge_atTop 2
  filter_upwards [eventually_ge_atTop T₀, hL2, hdecay, ha, hconj] with T hT hL hd ha' hc
  have H : TailHyp Z P T A₀ (C₁ T) :=
    { hT := hT, hL := hL, hA₀ := hA₀, hloc := hloc, hC₁ := hC₁ T, hdecay := hd }
  exact H.tailInputs ha' hc
