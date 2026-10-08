-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_3
-- name    : CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_3
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T01:37:30.512277+00:00
-- url     : https://prove2.me/theorems/d1f43fae-00f8-4be1-ac7c-8a97c65c16ca
-- title:
--   Support-controlled limits and Rényi bounds for faithful approximations
-- statement:
--   All operator spaces in the entropy statements are finite-dimensional, complex, and nonzero. For $\alpha>1$, $\rho,\sigma\ge0$ and $\ker\sigma\subseteq\ker\rho$,
--   $$
--   Q_\alpha(\rho+\varepsilon I\Vert\sigma+\varepsilon I)\to Q_\alpha(\rho\Vert\sigma)
--   \quad(\varepsilon\to0^+).
--   $$
--   If also $\rho\ne0$, the analogous limit holds for the real trace-normalized divergence $D_\alpha$ in nats. For $\alpha>0$ and positive semidefinite inputs,
--   $$
--   \operatorname{Re}Q_\alpha(\rho\Vert\sigma)=0
--   \iff\sigma^{(1-\alpha)/(2\alpha)}\rho\sigma^{(1-\alpha)/(2\alpha)}=0.
--   $$
--   In particular, its real part is nonzero for a positive-definite pair, and for $\alpha>1$ it is nonzero under support inclusion and $\rho\ne0$. Additional facts give nonnegativity of the real quasi-entropy, trace continuity under $\varepsilon I$ perturbations, and $D_\alpha(0\Vert\tau)=0$ for every real $\alpha$ and arbitrary $\tau$ under the total-logarithm convention.
--
--   For a CPTP map $\Phi$ and its faithful approximation $F_\lambda$, $0<\lambda\le1$, the part proves
--   $$
--   D_\alpha(F_\lambda(\rho)\Vert F_\lambda(\sigma))\le D_\alpha(\rho\Vert\sigma).
--   $$
--   For $1/2\le\alpha<1$, the supplied premises are $\rho,\sigma\ge0$, $\rho\ne0$, $\sigma\ne0$ and $\operatorname{Re}Q_\alpha(\rho\Vert\sigma)\ne0$. For $\alpha>1$, they are $\rho,\sigma\ge0$, $\rho\ne0$ and support inclusion. In the below-one regime a CPTP map preserves nonvanishing of $\operatorname{Re}Q_\alpha$ for positive inputs with $\rho\ne0$ and nonvanishing input quasi-entropy. Finally, positive-definite perturbation paths $\rho+\varepsilon P,\sigma+\varepsilon P$ give continuity of $Q_\alpha$ and $D_\alpha$ for $\alpha>0$ when $\rho,\sigma,P>0$; no normalization of their traces is required.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedRenyiNonNeg.lean#L1280-L1775

import Mathlib.Algebra.Central.End
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unique
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.JointEigenspace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Trace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Mathlib.Topology.Algebra.Star.Unitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_HaarUnitary
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedQuasiJensen_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_2
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiRelativeEntropy_part_3
import Definitions.Def_CRCD_Quantum_QuantumEntropy_TensorCFC
import Definitions.Def_CRCD_Quantum_QuantumEntropy_YoungInequality_part_2
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState
import Definitions.Def_CRCD_Quantum_TraceInequality_BlockDiagonal
import Definitions.Def_CRCD_Quantum_TraceInequality_GeneralizedPerspectiveFunction
import Definitions.Def_CRCD_Quantum_TraceInequality_HilbertSchmidtOperatorSpace
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequality
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LiebAndoTrace_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzTheorem
import Definitions.Def_CRCD_Quantum_TraceInequality_OperatorGeometricMean

/-
Copyright (c) 2025-2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/





/-!
# Sandwiched Rényi divergence on non-negative operators (Frank–Lieb extension)

This file extends the sandwiched Rényi divergence `D_α(ρ ‖ σ)` from the
positive-definite case to **non-negative** `ρ, σ ≥ 0`, following the convention
of Frank–Lieb (arXiv:1306.5358v3, §I.A).

## Main definitions

* `suppLE ρ σ` — support condition `ker σ ≤ ker ρ` (equivalent to `supp ρ ⊂ supp σ`).
* `sandwichedRenyiDivNN α ρ σ` — Frank–Lieb extension on `EReal`: equals
  `sandwichedRenyiDiv α ρ σ` when `α < 1` or `suppLE ρ σ`, and `⊤ : EReal`
  when `α > 1` and `¬ suppLE ρ σ`.

## Main theorem

* `sandwichedRenyiDivNN_monotone` — **Theorem 1** (Frank–Lieb): for any CPTP map
  `E : CPTP ℋ ℋ`, any `α ∈ [1/2, 1) ∪ (1, ∞)`, and any non-negative `ρ, σ`,
  `D_α^{NN}(E ρ ‖ E σ) ≤ D_α^{NN}(ρ ‖ σ)`.

## Proof structure

The main theorem reduces via case analysis:

* `α > 1`, `¬ suppLE ρ σ`: RHS is `⊤`, trivial.
* otherwise: real-valued inequality, proven via the faithful-approximation
  `F_λ := (1−λ) E + λ · depolarizing` (faithful for `λ > 0`), the perturbed
  Theorem 1 for faithful channels (`sandwichedRenyiDiv_monotone_nonneg_perturbed`),
  and boundary continuity of `sandwichedRenyiDiv` as `ε → 0+`.
-/

namespace SandwichedRenyiRelativeEntropy

open QuantumState QuantumChannel MeasureTheory TensorProduct
open scoped ComplexOrder NNReal Topology

universe u

set_option linter.style.longLine false

/-! ### Support condition `suppLE` -/





/-! ### Frank–Lieb explicit formula -/



/-! ### Auxiliary spectral / order lemmas -/









/-! ### Support preservation under positive maps -/



/-! ### Outer-product helpers and the depolarizing-channel Kraus decomposition -/











/-! ### Faithful approximating channel `F_λ := (1−λ) E + λ · depolarizing` -/

















/-! ### Continuity of `CFC.rpow` and `sandwichedQuasi` on the full non-negative cone

For a **non-negative exponent** `p ≥ 0` the map `x ↦ x^p` is continuous on all of
`ℝ≥0` (no pseudo-inverse discontinuity at `0`), so `A ↦ CFC.rpow A p` is continuous
on the whole non-negative cone `{A | 0 ≤ A}`, not just on the strictly-positive
`pdSetLM`. This is the analytic engine for the `α < 1` boundary continuity, where the
exponents `β = (1−α)/(2α) > 0` and `α > 0` are both non-negative. -/















/-! ### Boundary continuity of `sandwichedRenyiDiv` along the perturbation path -/

/-! #### Eigenvector formulas for the continuous functional calculus -/



















/-- **Boundary-continuity of `sandwichedQuasi` (α > 1) under `suppLE`.** Under the support
    condition, `Q_α(ρ+εI ‖ σ+εI) → Q_α(ρ ‖ σ)` as `ε → 0⁺`. The pseudo-inverse blow-up of
    `(σ+εI)^β` (β < 0) on `ker σ` is killed by `suppLE` (`rpow_conj_tendsto_of_suppLE`); the
    outer `Tr(·^α)` is continuous on the non-negative cone (`α > 0`). -/
 lemma sandwichedQuasi_tendsto_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) :
    Filter.Tendsto
      (fun ε : ℝ => sandwichedQuasi α (ρ + (ε : ℂ) • (1 : L ℋ)) (σ + (ε : ℂ) • (1 : L ℋ)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedQuasi α ρ σ)) := by
  have hαpos : 0 < α := by linarith
  set β : ℝ := (1-α)/(2*α) with hβ
  have hM := _root_.SandwichedRenyiRelativeEntropy.rpow_conj_tendsto_of_suppLE hα_gt hρ hσ hsupp
  have hMnn : ∀ A B : L ℋ, 0 ≤ B → (0:L ℋ) ≤ CFC.rpow A β * B * CFC.rpow A β :=
    fun A B hB => conjugate_nonneg_of_nonneg hB CFC.rpow_nonneg
  have hcont : ContinuousWithinAt (fun X : L ℋ => Tr (CFC.rpow X α)) {X : L ℋ | 0 ≤ X}
      (CFC.rpow σ β * ρ * CFC.rpow σ β) := by
    have h1 : ContinuousOn (fun X : L ℋ => CFC.rpow X α) {X : L ℋ | 0 ≤ X} :=
      _root_.QCProve2mePrivate.Quantum_QuantumEntropy_SandwichedRenyiNonNeg_rpow_continuousOn_nonneg (le_of_lt hαpos)
    have h2 : Continuous (fun A : L ℋ => Tr A) := LinearMap.continuous_of_finiteDimensional _
    exact (h2.comp_continuousOn h1).continuousWithinAt (hMnn σ ρ hρ)
  have hMwithin : Filter.Tendsto
      (fun ε : ℝ => CFC.rpow (σ+(ε:ℂ)•(1:L ℋ)) β * (ρ+(ε:ℂ)•(1:L ℋ)) * CFC.rpow (σ+(ε:ℂ)•(1:L ℋ)) β)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (CFC.rpow σ β * ρ * CFC.rpow σ β) {X : L ℋ | 0 ≤ X}) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hM, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with ε hε
    have hε1 : (0:L ℋ) ≤ (ε:ℂ)•(1:L ℋ) :=
      smul_nonneg (Complex.zero_le_real.mpr (le_of_lt hε)) zero_le_one
    exact hMnn _ _ (add_nonneg hρ hε1)
  have hcomp := Filter.Tendsto.comp hcont hMwithin
  have heqQ : ∀ ρ' σ' : L ℋ,
      sandwichedQuasi α ρ' σ' = Tr (CFC.rpow (CFC.rpow σ' β * ρ' * CFC.rpow σ' β) α) := by
    intro ρ' σ'; rfl
  simp_rw [heqQ]
  exact hcomp

/-- **Orthogonality core**: for `0 < α` and `ρ, σ ≥ 0`, the (real part of the)
    quasi-entropy vanishes iff the conjugated operator does:
    `Q_α(ρ‖σ).re = 0 ↔ σ^β ρ σ^β = 0` (where `β = (1−α)/(2α)`). The latter is the
    operator form of orthogonality `ρ ⊥ σ`. -/
 lemma sandwichedQuasi_re_eq_zero_iff
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) :
    (sandwichedQuasi α ρ σ).re = 0 ↔
      CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α)) = 0 := by
  set β : ℝ := (1 - α) / (2 * α) with hβ
  set M : L ℋ := CFC.rpow σ β * ρ * CFC.rpow σ β with hM
  have hM_nn : (0 : L ℋ) ≤ M := _root_.SandwichedRenyiRelativeEntropy.rpow_conj_nonneg β hρ hσ
  have hMα_nn : (0 : L ℋ) ≤ CFC.rpow M α := CFC.rpow_nonneg
  have hQ_eq : sandwichedQuasi α ρ σ = Tr (CFC.rpow M α) := by
    unfold sandwichedQuasi; rw [← hβ, ← hM]
  rw [hQ_eq]
  constructor
  · intro htr
    have hMα0 : CFC.rpow M α = 0 := by
      by_contra hne
      exact absurd htr (ne_of_gt (trace_re_pos_of_ne_zero hMα_nn hne))
    have hαinv : α * (1 / α) = 1 := by rw [mul_one_div, div_self (ne_of_gt hα0)]
    have hcomp : CFC.rpow (CFC.rpow M α) (1 / α) = M := by
      have key := CFC.rpow_rpow_of_exponent_nonneg M α (1 / α) hα0.le (by positivity) hM_nn
      rw [hαinv, CFC.rpow_one M hM_nn] at key
      exact key
    rw [hMα0, CFC.zero_rpow (one_div_ne_zero (ne_of_gt hα0))] at hcomp
    exact hcomp.symm
  · intro hM0
    rw [hM0, CFC.zero_rpow (ne_of_gt hα0), map_zero, Complex.zero_re]

/-- **Support-overlap ⟹ `Q_α ≠ 0` (α > 1).** Under `suppLE ρ σ` with `ρ ≠ 0`, the
    quasi-entropy is non-zero. Indeed `Q_α.re = 0 ⟺ σ^β ρ σ^β = 0`; expanding in the
    eigenbasis of `σ`, this forces `⟨b_k, ρ b_i⟩ = 0` for all `i, k` (using `suppLE` to
    kill the `ker σ` directions and positivity of `eigᵢ^β` elsewhere), hence `ρ = 0`,
    contradicting `ρ ≠ 0`. -/
 lemma sandwichedQuasi_re_ne_zero_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α) {ρ σ : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) (hρ0 : ρ ≠ 0) :
    (sandwichedQuasi α ρ σ).re ≠ 0 := by
  intro hzre
  have hαpos : 0 < α := by linarith
  set β : ℝ := (1-α)/(2*α) with hβ
  rw [_root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_re_eq_zero_iff hαpos hρ hσ] at hzre
  apply hρ0
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hσ_pos : σ.IsPositive := (LinearMap.nonneg_iff_isPositive σ).mp hσ
  have hσ_sym : σ.IsSymmetric := hσ_pos.isSymmetric
  have hρ_sym : ρ.IsSymmetric := ((LinearMap.nonneg_iff_isPositive ρ).mp hρ).isSymmetric
  set b := hσ_sym.eigenvectorBasis hn with hb
  set eig := hσ_sym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hσ_pos.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ):ℂ) • b i := hσ_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have h_ker : ∀ k, eig k = 0 → ρ (b k) = 0 :=
    fun k hk => hsupp (LinearMap.mem_ker.mpr (by rw [h_eig_apply k, hk]; simp))
  have h_supp_zero : ∀ i j, (eig i = 0 ∨ eig j = 0) → inner ℂ (b j) (ρ (b i)) = (0:ℂ) := by
    intro i j hij
    rcases hij with hi | hj
    · rw [h_ker i hi]; simp
    · rw [show inner ℂ (b j) (ρ (b i)) = inner ℂ (ρ (b j)) (b i) from (hρ_sym (b j) (b i)).symm,
          h_ker j hj]; simp
  have hspec0 : ∀ i, eig i ∈ spectrum ℝ σ :=
    fun i => mem_spectrum_real_of_eigenvector (hb_ne i) (h_eig_apply i)
  have hS0b : ∀ i, CFC.rpow σ β (b i) = (((eig i)^β : ℝ):ℂ) • b i :=
    fun i => _root_.SandwichedRenyiRelativeEntropy.rpow_apply_eigenvector hσ β (h_eig_apply i) (hspec0 i)
  have hSsym : (CFC.rpow σ β).IsSymmetric :=
    ((LinearMap.nonneg_iff_isPositive _).mp CFC.rpow_nonneg).isSymmetric
  have hcoeff : ∀ i k, inner ℂ (b k) ((CFC.rpow σ β * ρ * CFC.rpow σ β) (b i))
      = (((eig i)^β : ℝ):ℂ) * (((eig k)^β : ℝ):ℂ) * inner ℂ (b k) (ρ (b i)) := by
    intro i k
    rw [Module.End.mul_apply, Module.End.mul_apply, hS0b i, map_smul, map_smul, inner_smul_right,
        show inner ℂ (b k) (CFC.rpow σ β (ρ (b i)))
          = inner ℂ (CFC.rpow σ β (b k)) (ρ (b i)) from (hSsym (b k) (ρ (b i))).symm,
        hS0b k, inner_smul_left, Complex.conj_ofReal]
    ring
  have hzero_all : ∀ i k, inner ℂ (b k) (ρ (b i)) = (0:ℂ) := by
    intro i k
    by_cases h : eig i = 0 ∨ eig k = 0
    · exact h_supp_zero i k h
    · push_neg at h
      have hi' : 0 < eig i := lt_of_le_of_ne (h_eig_nn i) (Ne.symm h.1)
      have hk' : 0 < eig k := lt_of_le_of_ne (h_eig_nn k) (Ne.symm h.2)
      have hc := hcoeff i k
      rw [hzre, LinearMap.zero_apply, inner_zero_right] at hc
      have hne : (((eig i)^β : ℝ):ℂ) * (((eig k)^β : ℝ):ℂ) ≠ 0 := by
        rw [← Complex.ofReal_mul]
        exact Complex.ofReal_ne_zero.mpr (ne_of_gt (mul_pos (Real.rpow_pos_of_pos hi' β)
          (Real.rpow_pos_of_pos hk' β)))
      exact (mul_eq_zero.mp hc.symm).resolve_left hne
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.zero_apply]
  conv_lhs => rw [← b.sum_repr' x]
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [LinearMap.map_smul,
      show ρ (b i) = ∑ k, inner ℂ (b k) (ρ (b i)) • b k from (b.sum_repr' (ρ (b i))).symm]
  rw [show (∑ k, inner ℂ (b k) (ρ (b i)) • b k) = 0 from
      Finset.sum_eq_zero fun k _ => by rw [hzero_all i k, zero_smul]]
  rw [smul_zero]

/-- Continuity of `Tr` on perturbed states: `Tr(ρ + εI) → Tr ρ` as `ε → 0+`. -/
 lemma trace_tendsto_perturbed
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (ρ : L ℋ) :
    Filter.Tendsto
      (fun ε : ℝ => (Tr (ρ + (ε : ℂ) • (1 : L ℋ)) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Tr ρ)) := by
  have h_eq : ∀ ε : ℝ,
      (Tr (ρ + (ε : ℂ) • (1 : L ℋ)) : ℂ) =
      Tr ρ + (ε : ℂ) * (Module.finrank ℂ ℋ : ℂ) := by
    intro ε
    rw [map_add, LinearMap.map_smul, LinearMap.trace_one, smul_eq_mul]
  simp_rw [h_eq]
  have h_real : Filter.Tendsto
      (fun ε : ℝ => Tr ρ + (ε : ℂ) * (Module.finrank ℂ ℋ : ℂ))
      (nhds 0) (nhds (Tr ρ + (0 : ℂ) * (Module.finrank ℂ ℋ : ℂ))) := by
    refine Filter.Tendsto.add tendsto_const_nhds ?_
    refine Filter.Tendsto.mul ?_ tendsto_const_nhds
    exact (Complex.continuous_ofReal.tendsto 0)
  simpa using h_real.mono_left nhdsWithin_le_nhds

/-- **Boundary-continuity** of `sandwichedRenyiDiv` for non-negative `ρ, σ` with `suppLE ρ σ`,
    `α > 1`, and `ρ ≠ 0`.

    Derived from `sandwichedQuasi_tendsto_of_suppLE` (continuity of the quasi-relative
    entropy under `suppLE`), continuity of `Tr`, and continuity of `log`. Under `ρ ≠ 0` the
    denominator `(Tr ρ).re > 0` (`trace_re_pos_of_ne_zero`) and, under `suppLE`, the numerator
    `Q_α(ρ‖σ).re ≠ 0` (`sandwichedQuasi_re_ne_zero_of_suppLE`), so the limiting quotient is a
    continuity point of `log`. -/
 lemma sandwichedRenyiDiv_tendsto_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) (hρ0 : ρ ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ => sandwichedRenyiDiv α (ρ + (ε : ℂ) • (1 : L ℋ)) (σ + (ε : ℂ) • (1 : L ℋ)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedRenyiDiv α ρ σ)) := by
  unfold sandwichedRenyiDiv
  have h_tr : (Tr ρ).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hρ hρ0)
  have h_Q : (sandwichedQuasi α ρ σ).re ≠ 0 :=
    _root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_re_ne_zero_of_suppLE hα_gt hρ hσ hsupp hρ0
  -- (1) `Q_α(ρ+εI ‖ σ+εI) → Q_α(ρ ‖ σ)` as ε → 0+ (deep step under `suppLE`).
  have hQ : Filter.Tendsto
      (fun ε : ℝ =>
        (sandwichedQuasi α (ρ + (ε : ℂ) • (1 : L ℋ))
          (σ + (ε : ℂ) • (1 : L ℋ))).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedQuasi α ρ σ).re) := by
    have hQ_C := _root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_tendsto_of_suppLE hα_gt hρ hσ hsupp
    exact (Complex.continuous_re.tendsto _).comp hQ_C
  -- (2) `Tr(ρ+εI) → Tr ρ` (immediate, linear).
  have hT : Filter.Tendsto
      (fun ε : ℝ => (Tr (ρ + (ε : ℂ) • (1 : L ℋ))).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Tr ρ).re) :=
    (Complex.continuous_re.tendsto _).comp (_root_.SandwichedRenyiRelativeEntropy.trace_tendsto_perturbed (ℋ := ℋ) ρ)
  -- (3)+(4) Quotient and `log`: continuous since both limits are nonzero.
  have hLog : Filter.Tendsto
      (fun ε : ℝ =>
        Real.log
          ((sandwichedQuasi α (ρ + (ε : ℂ) • (1 : L ℋ))
              (σ + (ε : ℂ) • (1 : L ℋ))).re /
            (Tr (ρ + (ε : ℂ) • (1 : L ℋ))).re))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re))) := by
    have hRatio : Filter.Tendsto
        (fun ε : ℝ =>
          (sandwichedQuasi α (ρ + (ε : ℂ) • (1 : L ℋ))
              (σ + (ε : ℂ) • (1 : L ℋ))).re /
            (Tr (ρ + (ε : ℂ) • (1 : L ℋ))).re)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds ((sandwichedQuasi α ρ σ).re / (Tr ρ).re)) :=
      Filter.Tendsto.div hQ hT h_tr
    have h_div_ne : (sandwichedQuasi α ρ σ).re / (Tr ρ).re ≠ 0 :=
      div_ne_zero h_Q h_tr
    exact (Real.continuousAt_log h_div_ne).tendsto.comp hRatio
  exact hLog.const_mul _

/-! ### Helpers for the `α < 1` main-theorem case -/

/-- `sandwichedRenyiDiv α 0 τ = 0`: with `ρ = 0`, `Tr ρ = 0` and `Real.log (· / 0) = 0`. -/
 lemma sandwichedRenyiDiv_zero_left
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (α : ℝ) (τ : L ℋ) :
    sandwichedRenyiDiv α (0 : L ℋ) τ = 0 := by
  unfold sandwichedRenyiDiv
  have h0 : (Tr (0 : L ℋ)).re = 0 := by simp
  rw [h0, div_zero, Real.log_zero, mul_zero]

/-- For positive-definite `ρ, σ` (in `pdSetLM`), the quasi-entropy is non-zero: `σ^β ρ σ^β`
    is a product of units (hence a unit, hence `≠ 0`), so by `sandwichedQuasi_re_eq_zero_iff`
    its `Q_α.re ≠ 0`. -/
lemma sandwichedQuasi_re_ne_zero_of_pdSetLM
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) {ρ σ : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) :
    (sandwichedQuasi α ρ σ).re ≠ 0 := by
  have hrpow_unit : IsUnit (CFC.rpow σ ((1 - α) / (2 * α))) :=
    isUnit_of_pdSetLM (pdSetLM_rpow_ne hσ)
  have hρ_unit : IsUnit ρ := isUnit_of_pdSetLM hρ
  intro hzero
  rw [_root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_re_eq_zero_iff hα0 (nonneg_of_pdSetLM hρ) (nonneg_of_pdSetLM hσ)] at hzero
  exact (((hrpow_unit.mul hρ_unit).mul hrpow_unit).ne_zero) hzero

/-- The real part of the quasi-entropy is non-negative (it is `Tr` of a non-negative operator). -/
 lemma sandwichedQuasi_re_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    (α : ℝ) (ρ σ : L ℋ) :
    0 ≤ (sandwichedQuasi α ρ σ).re := by
  have hpos : (0 : L ℋ) ≤ CFC.rpow
      (CFC.rpow σ ((1 - α) / (2 * α)) * ρ * CFC.rpow σ ((1 - α) / (2 * α))) α := CFC.rpow_nonneg
  have h := ((LinearMap.nonneg_iff_isPositive _).mp hpos).trace_nonneg
  rw [Complex.le_def] at h
  exact h.1

/-- **Faithful-approximation DPI** (`α < 1`): for each `λ ∈ (0,1]`, the faithful channel
    `F_λ` satisfies `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)`. Obtained by taking `ε → 0⁺` in the
    perturbed PD inequality (`F_λρ, F_λσ` are positive-definite). -/
 lemma sandwichedRenyiDiv_faithfulApprox_le
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0) (hσ0 : σ ≠ 0)
    (hQρσ : (sandwichedQuasi α ρ σ).re ≠ 0)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    sandwichedRenyiDiv α ((faithfulApprox E lam hlam0.le hlam1).toFun ρ)
        ((faithfulApprox E lam hlam0.le hlam1).toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  have hTrρ : (Tr ρ).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hρ hρ0)
  set F := faithfulApprox E lam hlam0.le hlam1 with hF
  have hF1 : F.toFun 1 ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_one_pdSetLM E hlam0 hlam1
  have hFρ_pd : F.toFun ρ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hρ hρ0
  have hFσ_pd : F.toFun σ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hσ hσ0
  have hFρ_nn : (0 : L 𝒦) ≤ F.toFun ρ := nonneg_of_pdSetLM hFρ_pd
  have hFσ_nn : (0 : L 𝒦) ≤ F.toFun σ := nonneg_of_pdSetLM hFσ_pd
  have hF1_nn : (0 : L 𝒦) ≤ F.toFun 1 := nonneg_of_pdSetLM hF1
  have hQF : (sandwichedQuasi α (F.toFun ρ) (F.toFun σ)).re ≠ 0 :=
    sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hFρ_pd hFσ_pd
  have hTrFρ : (Tr (F.toFun ρ)).re ≠ 0 :=
    ne_of_gt (trace_re_pos_of_ne_zero hFρ_nn (isUnit_of_pdSetLM hFρ_pd).ne_zero)
  have h_pert : ∀ ε : ℝ, 0 < ε →
      sandwichedRenyiDiv α (F.toFun ρ + (ε : ℂ) • F.toFun 1) (F.toFun σ + (ε : ℂ) • F.toFun 1)
        ≤ sandwichedRenyiDiv α (ρ + (ε : ℂ) • (1 : L ℋ)) (σ + (ε : ℂ) • (1 : L ℋ)) := by
    intro ε hε
    have hpd := sandwichedRenyiDiv_monotone_nonneg_perturbed F hα_ge (ne_of_lt hα_lt) hρ hσ hF1 hε
    have hsmul := LinearMap.map_smul F.toCompletelyPositiveMap.toLinearMap (ε : ℂ) (1 : L ℋ)
    have eρ : F.toFun (ρ + (ε : ℂ) • (1 : L ℋ)) = F.toFun ρ + (ε : ℂ) • F.toFun (1 : L ℋ) := by
      have h1 := LinearMap.map_add F.toCompletelyPositiveMap.toLinearMap ρ ((ε : ℂ) • (1 : L ℋ))
      rw [hsmul] at h1; exact h1
    have eσ : F.toFun (σ + (ε : ℂ) • (1 : L ℋ)) = F.toFun σ + (ε : ℂ) • F.toFun (1 : L ℋ) := by
      have h1 := LinearMap.map_add F.toCompletelyPositiveMap.toLinearMap σ ((ε : ℂ) • (1 : L ℋ))
      rw [hsmul] at h1; exact h1
    rw [eρ, eσ] at hpd
    exact hpd
  have h_RHS := _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_tendsto_nonneg_lt hα0 hα_lt hρ hσ zero_le_one hQρσ hTrρ
  have h_LHS := _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_tendsto_nonneg_lt hα0 hα_lt hFρ_nn hFσ_nn hF1_nn hQF hTrFρ
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  exact le_of_tendsto_of_tendsto h_LHS h_RHS
    (Filter.eventually_of_mem self_mem_nhdsWithin h_pert)

/-- **Orthogonality reflection** (`α < 1`): a CPTP map cannot create orthogonality.
    If `ρ ≠ 0` and `Q_α(ρ‖σ) ≠ 0` (i.e. `ρ`, `σ` are not orthogonal), then
    `Q_α(Eρ‖Eσ) ≠ 0`.

    **Proof** (no Stinespring needed): the faithful DPI gives, for each `λ ∈ (0,1]`,
    `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)`; since `α < 1` (so `1/(α−1) < 0`) and `Tr(F_λρ) = Tr ρ`,
    this is equivalent to `Q_α(ρ‖σ) ≤ Q_α(F_λρ ‖ F_λσ)`. As `λ → 0⁺`, `Q_α(F_λρ‖F_λσ) →
    Q_α(Eρ‖Eσ)` by nonneg-cone continuity, so `0 < Q_α(ρ‖σ) ≤ Q_α(Eρ‖Eσ)`. -/
 lemma sandwichedQuasi_re_ne_zero_of_CPTP
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ} (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hQ : (sandwichedQuasi α ρ σ).re ≠ 0) :
    (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≠ 0 := by
  have hα0 : 0 < α := by linarith
  have hαm : α - 1 < 0 := by linarith
  have hTrρ_pos : 0 < (Tr ρ).re := trace_re_pos_of_ne_zero hρ hρ0
  have hb_pos : 0 < (sandwichedQuasi α ρ σ).re :=
    lt_of_le_of_ne (_root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_re_nonneg α ρ σ) (Ne.symm hQ)
  have hβne : (1 - α) / (2 * α) ≠ 0 := div_ne_zero (by linarith) (by positivity)
  have hσ0 : σ ≠ 0 := by
    intro h
    apply hQ
    rw [_root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_re_eq_zero_iff hα0 hρ hσ, h, CFC.zero_rpow hβne, zero_mul, mul_zero]
  -- `Q_α(ρ‖σ) ≤ Q_α(F_λρ ‖ F_λσ)` for each `λ`.
  have hQ_ge : ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
      (sandwichedQuasi α ρ σ).re ≤
        (sandwichedQuasi α ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ)).re := by
    rintro ⟨lam, hlam0, hlam1⟩
    simp only
    set F := faithfulApprox E lam hlam0.le hlam1 with hF
    have hFρ_pd : F.toFun ρ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hρ hρ0
    have hFσ_pd : F.toFun σ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hσ hσ0
    have ha_pos : 0 < (sandwichedQuasi α (F.toFun ρ) (F.toFun σ)).re :=
      lt_of_le_of_ne (_root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_re_nonneg _ _ _)
        (Ne.symm (sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hFρ_pd hFσ_pd))
    have hTrF : (Tr (F.toFun ρ)).re = (Tr ρ).re := by
      rw [← F.trace_map ρ]
    have hD := _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_faithfulApprox_le E hα_ge hα_lt hρ hσ hρ0 hσ0 hQ hlam0 hlam1
    -- Convert `D_F ≤ D_ρ` to `Q_ρ ≤ Q_F`.
    unfold sandwichedRenyiDiv at hD
    rw [hTrF] at hD
    -- `(1/(α-1)) log (Q_F/t) ≤ (1/(α-1)) log (Q_ρ/t)` with `1/(α-1) < 0` ⟹ flip.
    have hlog : Real.log ((sandwichedQuasi α ρ σ).re / (Tr ρ).re) ≤
        Real.log ((sandwichedQuasi α (F.toFun ρ) (F.toFun σ)).re / (Tr ρ).re) := by
      have hinv_neg : 1 / (α - 1) < 0 := one_div_neg.mpr hαm
      by_contra hcon
      push_neg at hcon
      exact absurd hD (not_le.mpr (by
        apply mul_lt_mul_of_neg_left hcon hinv_neg))
    rw [Real.log_le_log_iff (by positivity) (by positivity),
        div_le_div_iff_of_pos_right hTrρ_pos] at hlog
    exact hlog
  -- `λ → 0⁺`: `Q_α(F_λρ‖F_λσ).re → Q_α(Eρ‖Eσ).re`.
  have hEρ : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ : (0 : L 𝒦) ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
  have hcont := sandwichedQuasi_re_continuousOn_nonneg (ℋ := 𝒦) hα0 hα_lt.le
  have hcwa : ContinuousWithinAt
      (Function.uncurry (fun (ρ σ : L 𝒦) => (sandwichedQuasi α ρ σ).re))
      ({A : L 𝒦 | 0 ≤ A} ×ˢ {A : L 𝒦 | 0 ≤ A}) (E.toFun ρ, E.toFun σ) :=
    hcont (E.toFun ρ, E.toFun σ) ⟨hEρ, hEσ⟩
  have hpair : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        (((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ),
         ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ)))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhdsWithin (E.toFun ρ, E.toFun σ) ({A : L 𝒦 | 0 ≤ A} ×ˢ {A : L 𝒦 | 0 ≤ A})) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨(faithfulApprox_tendsto E ρ).prodMk_nhds (faithfulApprox_tendsto E σ), ?_⟩
    filter_upwards with l
    exact Set.mk_mem_prod
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM E l.property.1 l.property.2 hρ hρ0))
      (nonneg_of_pdSetLM (faithfulApprox_pdSetLM E l.property.1 l.property.2 hσ hσ0))
  have hlim := hcwa.tendsto.comp hpair
  haveI : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (nhdsWithin 0 (Set.Ioi 0))).NeBot := by
    refine Filter.comap_neBot fun t ht => ?_
    obtain ⟨U, hU_open, hU0, hU_sub⟩ := mem_nhdsWithin.mp ht
    obtain ⟨δ, hδ_pos, hball⟩ := Metric.mem_nhds_iff.mp (hU_open.mem_nhds hU0)
    have hx_pos : (0 : ℝ) < min (δ / 2) 1 := lt_min (by positivity) one_pos
    refine ⟨⟨min (δ / 2) 1, hx_pos, min_le_right _ _⟩, ?_⟩
    apply hU_sub
    refine ⟨hball ?_, hx_pos⟩
    simp only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hx_pos]
    exact lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hle : (sandwichedQuasi α ρ σ).re ≤ (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re :=
    ge_of_tendsto hlim (Filter.Eventually.of_forall hQ_ge)
  exact ne_of_gt (lt_of_lt_of_le hb_pos hle)

/-! ### Real-valued monotonicity (used in the main theorem) -/

/-- `Q_α` continuity along a pd perturbation path `ε ↦ (ρ+εP, σ+εP)` (all pd). -/
 lemma sandwichedQuasi_tendsto_pd
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (_hα0 : 0 < α) {ρ σ P : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) (hP : P ∈ pdSetLM (ℋ := ℋ)) :
    Filter.Tendsto
      (fun ε : ℝ => (sandwichedQuasi α (ρ + (ε : ℂ) • P) (σ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedQuasi α ρ σ).re) := by
  have hcont := sandwichedQuasi_re_continuousOn_pdSetLM (ℋ_aux := ℋ) α
  set S : Set (L ℋ × L ℋ) := pdSetLM (ℋ := ℋ) ×ˢ pdSetLM (ℋ := ℋ) with hS
  set g : ℝ → L ℋ × L ℋ := fun ε => (ρ + (ε : ℂ) • P, σ + (ε : ℂ) • P) with hg_def
  have hg_cont : Continuous g := by fun_prop
  have hg0 : g 0 = (ρ, σ) := by simp [hg_def]
  have hg_tendsto : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin (ρ, σ) S) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · rw [← hg0]; exact (hg_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεP : (ε : ℂ) • P ∈ pdSetLM (ℋ := ℋ) := pdSetLM_pos_smul hP hε
      refine Set.mk_mem_prod ?_ ?_
      · rw [add_comm]; exact pdSetLM_add_nonneg (nonneg_of_pdSetLM hεP) hρ
      · rw [add_comm]; exact pdSetLM_add_nonneg (nonneg_of_pdSetLM hεP) hσ
  have hcwa : ContinuousWithinAt
      (Function.uncurry (fun (ρ σ : L ℋ) => (sandwichedQuasi α ρ σ).re)) S (ρ, σ) :=
    hcont (ρ, σ) ⟨hρ, hσ⟩
  have hcomp := (hcwa.tendsto).comp hg_tendsto
  simpa only [Function.comp_def, Function.uncurry, hg_def] using hcomp

/-- `D_α` continuity along a pd perturbation path. -/
 lemma sandwichedRenyiDiv_tendsto_pd
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) {ρ σ P : L ℋ}
    (hρ : ρ ∈ pdSetLM (ℋ := ℋ)) (hσ : σ ∈ pdSetLM (ℋ := ℋ)) (hP : P ∈ pdSetLM (ℋ := ℋ)) :
    Filter.Tendsto
      (fun ε : ℝ => sandwichedRenyiDiv α (ρ + (ε : ℂ) • P) (σ + (ε : ℂ) • P))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedRenyiDiv α ρ σ)) := by
  unfold sandwichedRenyiDiv
  have hQc := _root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_tendsto_pd hα0 hρ hσ hP
  have hTr0 : (Tr ρ).re ≠ 0 :=
    ne_of_gt (trace_re_pos_of_ne_zero (nonneg_of_pdSetLM hρ) (isUnit_of_pdSetLM hρ).ne_zero)
  have hQ0 : (sandwichedQuasi α ρ σ).re ≠ 0 := sandwichedQuasi_re_ne_zero_of_pdSetLM hα0 hρ hσ
  have hTc : Filter.Tendsto (fun ε : ℝ => (Tr (ρ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Tr ρ).re) := by
    have hform : ∀ ε : ℝ, (Tr (ρ + (ε : ℂ) • P)).re = (Tr ρ).re + ε * (Tr P).re := by
      intro ε
      rw [map_add, map_smul, smul_eq_mul, Complex.add_re, Complex.re_ofReal_mul]
    simp_rw [hform]
    have h2 : Filter.Tendsto (fun ε : ℝ => (Tr ρ).re + ε * (Tr P).re)
        (nhds 0) (nhds ((Tr ρ).re + 0 * (Tr P).re)) :=
      tendsto_const_nhds.add ((continuous_id.mul continuous_const).tendsto 0)
    simpa using h2.mono_left nhdsWithin_le_nhds
  have hRatio : Filter.Tendsto
      (fun ε : ℝ => (sandwichedQuasi α (ρ + (ε : ℂ) • P) (σ + (ε : ℂ) • P)).re /
        (Tr (ρ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds ((sandwichedQuasi α ρ σ).re / (Tr ρ).re)) :=
    Filter.Tendsto.div hQc hTc hTr0
  have hLog := (Real.continuousAt_log (div_ne_zero hQ0 hTr0)).tendsto.comp hRatio
  exact hLog.const_mul _

/-- **Faithful-approximation DPI** (`α > 1`): for each `λ ∈ (0,1]`, `D_α(F_λρ ‖ F_λσ) ≤
    D_α(ρ‖σ)`. Take `ε → 0⁺` in the perturbed PD inequality: the LHS limit at the PD pair
    `(F_λρ, F_λσ)` uses PD-continuity, the RHS limit uses `suppLE`-boundary continuity. -/
 lemma sandwichedRenyiDiv_faithfulApprox_le_gt
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0) (hsupp : suppLE ρ σ)
    {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    sandwichedRenyiDiv α ((faithfulApprox E lam hlam0.le hlam1).toFun ρ)
        ((faithfulApprox E lam hlam0.le hlam1).toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  have hα_ge : (1 : ℝ) / 2 ≤ α := by linarith
  have hα0 : 0 < α := by linarith
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    apply hρ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp (hsupp (LinearMap.mem_ker.mpr (by simp)))
  set F := faithfulApprox E lam hlam0.le hlam1 with hF
  have hF1 : F.toFun 1 ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_one_pdSetLM E hlam0 hlam1
  have hFρ_pd : F.toFun ρ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hρ hρ0
  have hFσ_pd : F.toFun σ ∈ pdSetLM (ℋ := 𝒦) := faithfulApprox_pdSetLM E hlam0 hlam1 hσ hσ0
  have h_pert : ∀ ε : ℝ, 0 < ε →
      sandwichedRenyiDiv α (F.toFun ρ + (ε : ℂ) • F.toFun 1) (F.toFun σ + (ε : ℂ) • F.toFun 1)
        ≤ sandwichedRenyiDiv α (ρ + (ε : ℂ) • (1 : L ℋ)) (σ + (ε : ℂ) • (1 : L ℋ)) := by
    intro ε hε
    have hpd := sandwichedRenyiDiv_monotone_nonneg_perturbed F hα_ge (ne_of_gt hα_gt) hρ hσ hF1 hε
    have hsmul := LinearMap.map_smul F.toCompletelyPositiveMap.toLinearMap (ε : ℂ) (1 : L ℋ)
    have eρ : F.toFun (ρ + (ε : ℂ) • (1 : L ℋ)) = F.toFun ρ + (ε : ℂ) • F.toFun (1 : L ℋ) := by
      have h1 := LinearMap.map_add F.toCompletelyPositiveMap.toLinearMap ρ ((ε : ℂ) • (1 : L ℋ))
      rw [hsmul] at h1; exact h1
    have eσ : F.toFun (σ + (ε : ℂ) • (1 : L ℋ)) = F.toFun σ + (ε : ℂ) • F.toFun (1 : L ℋ) := by
      have h1 := LinearMap.map_add F.toCompletelyPositiveMap.toLinearMap σ ((ε : ℂ) • (1 : L ℋ))
      rw [hsmul] at h1; exact h1
    rw [eρ, eσ] at hpd
    exact hpd
  have h_RHS := _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_tendsto_of_suppLE hα_gt hρ hσ hsupp hρ0
  have h_LHS := _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_tendsto_pd hα0 hFρ_pd hFσ_pd hF1
  haveI : (nhdsWithin (0 : ℝ) (Set.Ioi 0)).NeBot := nhdsWithin_Ioi_neBot (le_refl 0)
  exact le_of_tendsto_of_tendsto h_LHS h_RHS
    (Filter.eventually_of_mem self_mem_nhdsWithin h_pert)
end SandwichedRenyiRelativeEntropy


/- Mechanically delaborated from the original compiled Lean 4.30 ConstantInfo. -/
public theorem SandwichedRenyiRelativeEntropy.sandwichedQuasi_re_ne_zero_of_CPTP._simp_1_2.{u} :
∀ {α : Type u} [inst : PseudoMetricSpace.{u} α] {x y : α} {ε : Real},
  Eq.{1} (Membership.mem.{u, u} (Metric.ball.{u} x ε) y) (LT.lt.{0} (Dist.dist.{u} y x) ε) :=
fun {α} [PseudoMetricSpace.{u} α] {x y} {ε} => propext Metric.mem_ball.{u}


