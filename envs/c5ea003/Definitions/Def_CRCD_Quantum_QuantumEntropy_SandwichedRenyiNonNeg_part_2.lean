-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_2
-- name    : CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_2
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T01:36:35.929009+00:00
-- url     : https://prove2.me/theorems/23820188-4a00-427e-99bc-d3ee8b22615e
-- title:
--   Faithful approximation, spectral calculus, and boundary continuity below order one
-- statement:
--   Let $\Phi:L(H)\to L(K)$ be CPTP on nonzero finite-dimensional complex Hilbert spaces, and $F_\lambda=(1-\lambda)\Phi+\lambda\Delta_{H,K}$. For $0<\lambda\le1$, $F_\lambda(I_H)>0$ and $F_\lambda(\rho)>0$ whenever $\rho\ge0$, $\rho\ne0$. For every operator $X$, $F_\lambda(X)\to\Phi(X)$ as $\lambda\to0^+$ through $(0,1]$. A nonzero positive semidefinite operator has strictly positive real trace.
--
--   Every nonnegative real power is continuous on the positive semidefinite cone. Consequently $\operatorname{Re}Q_\alpha$ is jointly continuous there for $0<\alpha\le1$. If $0<\alpha<1$, $\rho,\sigma,P\ge0$, $\operatorname{Re}Q_\alpha(\rho\Vert\sigma)\ne0$ and $\operatorname{Re}\operatorname{Tr}\rho\ne0$, then
--   $$
--   \lim_{\varepsilon\to0^+}D_\alpha(\rho+\varepsilon P\Vert\sigma+\varepsilon P)
--   =D_\alpha(\rho\Vert\sigma).
--   $$
--   The same nonvanishing conditions give joint continuity within the positive semidefinite cone; no support inclusion is needed. $D_\alpha$ is the real trace-normalized divergence in nats.
--
--   For $\alpha>1$, positive semidefinite $\rho,\sigma$ with $\ker\sigma\subseteq\ker\rho$, and $\beta=(1-\alpha)/(2\alpha)$, this part establishes the operator limit
--   $$
--   (\sigma+\varepsilon I)^\beta(\rho+\varepsilon I)(\sigma+\varepsilon I)^\beta
--   \longrightarrow\sigma^\beta\rho\sigma^\beta\quad(\varepsilon\to0^+).
--   $$
--   The spectral facts include finite real spectrum, $f(A)v=f(\mu)v$ for self-adjoint $A$, an eigenvector $Av=\mu v$, and $\mu\in\operatorname{spec}_{\mathbb R}A$, for arbitrary real functions $f$; the power version applies to $A\ge0$ and every real exponent. A nonzero eigenvector places its real eigenvalue in that spectrum. The part introduces the continuous linear map $v\mapsto|v\rangle\langle u|$ for fixed $u$, and proves the associated elementary eigenvector formulas.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedRenyiNonNeg.lean#L679-L1278

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
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_1
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









/-- For a non-zero non-negative operator, the real part of the trace is strictly positive. -/
lemma trace_re_pos_of_ne_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {ρ : L ℋ} (hρ : 0 ≤ ρ) (hne : ρ ≠ 0) :
    0 < (Tr ρ).re := by
  have hρ_pos : ρ.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hρ
  have hρ_sym := hρ_pos.isSymmetric
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  rw [show (Tr ρ).re = ∑ i, hρ_sym.eigenvalues hn i from
        hρ_sym.re_trace_eq_sum_eigenvalues hn]
  have h_eig_nn : ∀ i, 0 ≤ hρ_sym.eigenvalues hn i := fun i => hρ_pos.nonneg_eigenvalues hn i
  rcases eq_or_lt_of_le (Finset.sum_nonneg (fun i _ => h_eig_nn i)) with hsum | hsum
  · exfalso
    apply hne
    have h_all : ∀ i, hρ_sym.eigenvalues hn i = 0 := by
      intro i
      have hle : hρ_sym.eigenvalues hn i ≤ ∑ j, hρ_sym.eigenvalues hn j :=
        Finset.single_le_sum (f := fun j => hρ_sym.eigenvalues hn j)
          (fun j _ => h_eig_nn j) (Finset.mem_univ i)
      linarith [h_eig_nn i, hsum, hle]
    have h_apply : ∀ i, ρ (hρ_sym.eigenvectorBasis hn i) = 0 := by
      intro i
      rw [hρ_sym.apply_eigenvectorBasis hn i, h_all i]; simp
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    conv_lhs => rw [← (hρ_sym.eigenvectorBasis hn).sum_repr x]
    rw [map_sum]
    exact Finset.sum_eq_zero (fun i _ => by rw [LinearMap.map_smul, h_apply i, smul_zero])
  · exact hsum

/-- For `0 < λ ≤ 1`, the approximating channel is faithful (`F_λ 1_ℋ` is positive definite
    in the target `𝒦`). -/
lemma faithfulApprox_one_pdSetLM
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1) :
    (faithfulApprox E lam hlam0.le hlam1).toFun (1 : L ℋ) ∈ pdSetLM (ℋ := 𝒦) := by
  -- `F_λ 1_ℋ = (1-λ) E 1 + λ • (Tr 1_ℋ / d_𝒦) • 1_𝒦 = (1-λ) E 1 + (λ·d_ℋ/d_𝒦) • 1_𝒦`.
  have hdℋ_pos : 0 < (Module.finrank ℂ ℋ : ℝ) := by exact_mod_cast Module.finrank_pos
  have hd𝒦_pos : 0 < (Module.finrank ℂ 𝒦 : ℝ) := by exact_mod_cast Module.finrank_pos
  have h_F1 : (faithfulApprox E lam hlam0.le hlam1).toFun (1 : L ℋ) =
      ((1 - lam : ℝ) : ℂ) • E.toFun (1 : L ℋ) +
        ((lam * Module.finrank ℂ ℋ / Module.finrank ℂ 𝒦 : ℝ) : ℂ) • (1 : L 𝒦) := by
    change ((1 - lam : ℝ) : ℂ) • E.toFun (1 : L ℋ) +
         ((lam : ℝ) : ℂ) •
           ((Tr (1 : L ℋ) / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)) = _
    rw [smul_smul, LinearMap.trace_one]
    congr 2
    push_cast
    ring
  rw [h_F1]
  -- `(1-λ) E 1 ≥ 0` (since `1 ≥ 0`, `E` preserves `≥ 0`, `1-λ ≥ 0`).
  have h_E1_nn : (0 : L 𝒦) ≤ E.toFun (1 : L ℋ) :=
    map_nonneg E.toCompletelyPositiveMap zero_le_one
  have h_coef_nn : (0 : ℂ) ≤ ((1 - lam : ℝ) : ℂ) :=
    Complex.zero_le_real.mpr (by linarith)
  have h_first_nn : (0 : L 𝒦) ≤ ((1 - lam : ℝ) : ℂ) • E.toFun (1 : L ℋ) :=
    (LinearMap.nonneg_iff_isPositive _).mpr
      (((LinearMap.nonneg_iff_isPositive _).mp h_E1_nn).smul_of_nonneg h_coef_nn)
  -- `(λ·d_ℋ/d_𝒦) • 1_𝒦 ∈ pdSetLM` (positive scalar).
  have h_second_pd :
      ((lam * Module.finrank ℂ ℋ / Module.finrank ℂ 𝒦 : ℝ) : ℂ) • (1 : L 𝒦) ∈ pdSetLM (ℋ := 𝒦) :=
    pos_smul_one_pdSetLM (by positivity)
  exact pdSetLM_add_nonneg h_first_nn h_second_pd

/-- For `0 < λ ≤ 1` and `ρ ≠ 0` non-negative, `F_λ ρ` is positive definite:
    `F_λ ρ = (1−λ)·Eρ + λ·(Tr ρ / d)·1`, where the second summand is `(positive real)·1 ∈ pdSetLM`
    (since `Tr ρ > 0`) and the first is non-negative. -/
lemma faithfulApprox_pdSetLM
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {lam : ℝ} (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    {ρ : L ℋ} (hρ : 0 ≤ ρ) (hρ0 : ρ ≠ 0) :
    (faithfulApprox E lam hlam0.le hlam1).toFun ρ ∈ pdSetLM (ℋ := 𝒦) := by
  have hd_pos : 0 < (Module.finrank ℂ 𝒦 : ℝ) := by exact_mod_cast Module.finrank_pos
  have hTrρ_pos : 0 < (Tr ρ).re := trace_re_pos_of_ne_zero hρ hρ0
  -- `Tr ρ` is real (`ρ` non-negative, hence self-adjoint).
  have hρ_pos : ρ.IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hρ
  have hTr_im : (Tr ρ).im = 0 := by
    have h := hρ_pos.trace_nonneg
    rw [Complex.le_def] at h
    exact h.2.symm
  have hTr_real : Tr ρ = ((Tr ρ).re : ℂ) := by
    apply Complex.ext <;> simp [hTr_im]
  have hscalar : ((lam : ℝ) : ℂ) * (Tr ρ / (Module.finrank ℂ 𝒦 : ℂ)) =
      ((lam * (Tr ρ).re / Module.finrank ℂ 𝒦 : ℝ) : ℂ) := by
    set t : ℝ := (Tr ρ).re with ht
    rw [hTr_real]; push_cast; ring
  have h_Fρ : (faithfulApprox E lam hlam0.le hlam1).toFun ρ =
      ((1 - lam : ℝ) : ℂ) • E.toFun ρ +
        ((lam * (Tr ρ).re / Module.finrank ℂ 𝒦 : ℝ) : ℂ) • (1 : L 𝒦) := by
    change ((1 - lam : ℝ) : ℂ) • E.toFun ρ +
         ((lam : ℝ) : ℂ) • ((Tr ρ / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)) = _
    rw [smul_smul, hscalar]
  rw [h_Fρ]
  have hEρ_nn : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have h_first_nn : (0 : L 𝒦) ≤ ((1 - lam : ℝ) : ℂ) • E.toFun ρ :=
    (LinearMap.nonneg_iff_isPositive _).mpr
      (((LinearMap.nonneg_iff_isPositive _).mp hEρ_nn).smul_of_nonneg
        (Complex.zero_le_real.mpr (by linarith)))
  have h_second_pd :
      ((lam * (Tr ρ).re / Module.finrank ℂ 𝒦 : ℝ) : ℂ) • (1 : L 𝒦) ∈ pdSetLM (ℋ := 𝒦) :=
    pos_smul_one_pdSetLM (div_pos (mul_pos hlam0 hTrρ_pos) hd_pos)
  exact pdSetLM_add_nonneg h_first_nn h_second_pd

/-- `F_λ X → E X` as `λ → 0+`. -/
lemma faithfulApprox_tendsto
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) (X : L ℋ) :
    Filter.Tendsto
      (fun (lam : {l : ℝ // 0 < l ∧ l ≤ 1}) =>
        (faithfulApprox E lam.val lam.property.1.le lam.property.2).toFun X)
      (Filter.comap (fun lam : {l : ℝ // 0 < l ∧ l ≤ 1} => lam.val)
        (nhdsWithin 0 (Set.Ioi 0))) (nhds (E.toFun X)) := by
  -- Extend to all `lam : ℝ`: `g lam = (1-lam) • E X + lam • c` where `c = (Tr X / d_𝒦) • 1_𝒦`.
  let c : L 𝒦 := (Tr X / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)
  let g : ℝ → L 𝒦 :=
    fun lam => ((1 - lam : ℝ) : ℂ) • E.toFun X + ((lam : ℝ) : ℂ) • c
  -- The defining formula of `F_λ X` matches `g lam.val` definitionally.
  have h_F_eq : ∀ (lam : {l : ℝ // 0 < l ∧ l ≤ 1}),
      (faithfulApprox E lam.val lam.property.1.le lam.property.2).toFun X = g lam.val :=
    fun _ => rfl
  simp_rw [h_F_eq]
  -- `g` is continuous on ℝ.
  have hg_cont : Continuous g := by
    change Continuous (fun lam : ℝ =>
      ((1 - lam : ℝ) : ℂ) • E.toFun X + ((lam : ℝ) : ℂ) • c)
    fun_prop
  -- `g 0 = E.toFun X`.
  have hg_zero : g 0 = E.toFun X := by
    change ((1 - (0 : ℝ) : ℝ) : ℂ) • E.toFun X + (((0 : ℝ)) : ℂ) • c = E.toFun X
    simp
  -- Tendsto in ℝ at 0 (from the right) follows from continuity at 0.
  have h_real : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhds (E.toFun X)) := by
    rw [← hg_zero]
    exact (hg_cont.tendsto 0).mono_left nhdsWithin_le_nhds
  -- Transfer along the subtype projection via `comap`.
  exact h_real.comp Filter.tendsto_comap

/-! ### Continuity of `CFC.rpow` and `sandwichedQuasi` on the full non-negative cone

For a **non-negative exponent** `p ≥ 0` the map `x ↦ x^p` is continuous on all of
`ℝ≥0` (no pseudo-inverse discontinuity at `0`), so `A ↦ CFC.rpow A p` is continuous
on the whole non-negative cone `{A | 0 ≤ A}`, not just on the strictly-positive
`pdSetLM`. This is the analytic engine for the `α < 1` boundary continuity, where the
exponents `β = (1−α)/(2α) > 0` and `α > 0` are both non-negative. -/

/-- For a non-negative exponent `p`, `A ↦ CFC.rpow A p` is continuous on the
    non-negative cone `{A | 0 ≤ A}`. -/
 lemma _root_.QCProve2mePrivate.Quantum_QuantumEntropy_SandwichedRenyiNonNeg_rpow_continuousOn_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {p : ℝ} (hp : 0 ≤ p) :
    ContinuousOn (fun A : L ℋ => CFC.rpow A p) {A : L ℋ | 0 ≤ A} := by
  have h_nhds : (Set.univ : Set ℝ≥0) ∈ 𝓝ˢ (⋃ A ∈ {A : L ℋ | 0 ≤ A}, spectrum ℝ≥0 A) :=
    Filter.univ_mem
  have h_id_cont : ContinuousOn (fun A : L ℋ => A) {A : L ℋ | 0 ≤ A} := continuousOn_id
  have h_nn : ∀ A ∈ {A : L ℋ | 0 ≤ A}, (0 : L ℋ) ≤ A := fun _ hA => hA
  have h_f_cont : ContinuousOn (fun x : ℝ≥0 => x ^ p) (Set.univ) :=
    NNReal.continuousOn_rpow_const (.inr hp)
  exact h_id_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ p))
    h_nhds (ha' := h_nn) (hf := h_f_cont)

/-- For non-negative `ρ, σ`, the conjugate `σ^β ρ σ^β` is non-negative. -/
 lemma rpow_conj_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (β : ℝ) {ρ σ : L ℋ}
    (hρ : 0 ≤ ρ) (_hσ : 0 ≤ σ) :
    (0 : L ℋ) ≤ CFC.rpow σ β * ρ * CFC.rpow σ β :=
  conjugate_nonneg_of_nonneg hρ CFC.rpow_nonneg

/-- Continuity of `(ρ, σ) ↦ σ^β ρ σ^β` on the non-negative cone, for `β ≥ 0`. -/
 lemma rpow_conj_continuousOn_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {β : ℝ} (hβ : 0 ≤ β) :
    ContinuousOn (fun p : L ℋ × L ℋ => CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) := by
  have h_rpow_snd : ContinuousOn (fun p : L ℋ × L ℋ => CFC.rpow p.2 β)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) :=
    (_root_.QCProve2mePrivate.Quantum_QuantumEntropy_SandwichedRenyiNonNeg_rpow_continuousOn_nonneg hβ).comp continuousOn_snd
      (fun _ hx => (Set.mem_prod.mp hx).2)
  have h_fst : ContinuousOn (fun p : L ℋ × L ℋ => p.1)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) := continuousOn_fst
  exact (h_rpow_snd.mul h_fst).mul h_rpow_snd

/-- **Joint continuity of `(sandwichedQuasi α · ·).re` on the full non-negative cone**,
    valid for `0 < α ≤ 1` (both exponents `β = (1−α)/(2α) ≥ 0` and `α ≥ 0` are
    non-negative, so no pseudo-inverse discontinuity occurs). This is the `α < 1`
    analogue of `sandwichedQuasi_re_continuousOn_pdSetLM`. -/
lemma sandwichedQuasi_re_continuousOn_nonneg
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ContinuousOn (Function.uncurry (fun (ρ σ : L ℋ) => (sandwichedQuasi α ρ σ).re))
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) := by
  set β : ℝ := (1 - α) / (2 * α) with hβ_def
  have hβ_nn : 0 ≤ β := by
    rw [hβ_def]; apply div_nonneg (by linarith) (by positivity)
  have h_inner_cont :
      ContinuousOn (fun p : L ℋ × L ℋ => CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)
        ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) :=
    _root_.SandwichedRenyiRelativeEntropy.rpow_conj_continuousOn_nonneg hβ_nn
  have h_inner_nn : ∀ p ∈ {A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A},
      (0 : L ℋ) ≤ CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β := by
    rintro ⟨ρ, σ⟩ ⟨hρ, hσ⟩
    exact _root_.SandwichedRenyiRelativeEntropy.rpow_conj_nonneg β hρ hσ
  have h_nhds :
      (Set.univ : Set ℝ≥0) ∈
        𝓝ˢ (⋃ p ∈ {A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A},
          spectrum ℝ≥0 (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β)) :=
    Filter.univ_mem
  have h_f_cont : ContinuousOn (fun x : ℝ≥0 => x ^ α) (Set.univ) :=
    NNReal.continuousOn_rpow_const (.inr hα0.le)
  have h_pow_cont :
      ContinuousOn
        (fun p : L ℋ × L ℋ => CFC.rpow (CFC.rpow p.2 β * p.1 * CFC.rpow p.2 β) α)
        ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) :=
    h_inner_cont.cfc_nnreal_of_mem_nhdsSet (s := Set.univ) (f := (· ^ α))
      h_nhds (ha' := h_inner_nn) (hf := h_f_cont)
  have h_trace_cont : Continuous (fun A : L ℋ => Tr A) :=
    LinearMap.continuous_of_finiteDimensional _
  exact Complex.continuous_re.comp_continuousOn (h_trace_cont.comp_continuousOn h_pow_cont)

/-- For `0 < α ≤ 1`, `Q_α` is continuous along the non-negative perturbation path
    `ε ↦ (ρ + ε•P, σ + ε•P)` (with `P ≥ 0`) as `ε → 0⁺`. -/
 lemma sandwichedQuasi_tendsto_nonneg_lt
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) {ρ σ P : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hP : 0 ≤ P) :
    Filter.Tendsto
      (fun ε : ℝ => (sandwichedQuasi α (ρ + (ε : ℂ) • P) (σ + (ε : ℂ) • P)).re)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedQuasi α ρ σ).re) := by
  have hcont := sandwichedQuasi_re_continuousOn_nonneg (ℋ := ℋ) hα0 hα1
  set S : Set (L ℋ × L ℋ) := {A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A} with hS
  set g : ℝ → L ℋ × L ℋ := fun ε => (ρ + (ε : ℂ) • P, σ + (ε : ℂ) • P) with hg_def
  have hg_cont : Continuous g := by fun_prop
  have hg0 : g 0 = (ρ, σ) := by simp [hg_def]
  have hg_tendsto : Filter.Tendsto g (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin (ρ, σ) S) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · rw [← hg0]; exact (hg_cont.tendsto 0).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with ε hε
      have hεpos : (0 : ℝ) < ε := hε
      exact Set.mk_mem_prod
        (add_nonneg hρ (smul_nonneg (Complex.zero_le_real.mpr hεpos.le) hP))
        (add_nonneg hσ (smul_nonneg (Complex.zero_le_real.mpr hεpos.le) hP))
  have hcwa : ContinuousWithinAt
      (Function.uncurry (fun (ρ σ : L ℋ) => (sandwichedQuasi α ρ σ).re)) S (ρ, σ) :=
    hcont (ρ, σ) ⟨hρ, hσ⟩
  have hcomp := (hcwa.tendsto).comp hg_tendsto
  simpa only [Function.comp_def, Function.uncurry, hg_def] using hcomp

/-- **Boundary-continuity of `sandwichedRenyiDiv` for `α < 1`** along a non-negative
    perturbation direction `P`, at a point where `Q_α ≠ 0` and `Tr ρ ≠ 0`. No support
    condition is needed: the exponents are non-negative, so `Q_α` is jointly continuous
    on the whole non-negative cone. -/
 lemma sandwichedRenyiDiv_tendsto_nonneg_lt
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ σ P : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hP : 0 ≤ P)
    (hQ : (sandwichedQuasi α ρ σ).re ≠ 0) (hTr : (Tr ρ).re ≠ 0) :
    Filter.Tendsto
      (fun ε : ℝ => sandwichedRenyiDiv α (ρ + (ε : ℂ) • P) (σ + (ε : ℂ) • P))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (sandwichedRenyiDiv α ρ σ)) := by
  unfold sandwichedRenyiDiv
  have hQc := _root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_tendsto_nonneg_lt hα0 hα1.le hρ hσ hP
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
    Filter.Tendsto.div hQc hTc hTr
  have h_div_ne : (sandwichedQuasi α ρ σ).re / (Tr ρ).re ≠ 0 := div_ne_zero hQ hTr
  have hLog := (Real.continuousAt_log h_div_ne).tendsto.comp hRatio
  exact hLog.const_mul _

/-- **Joint continuity (within the non-negative cone) of `sandwichedRenyiDiv` for `α < 1`**
    at a point `(ρ₀, σ₀)` with `Q_α ≠ 0` and `Tr ρ₀ ≠ 0`. Used to pass both the
    `λ → 0⁺` (channel) and `ε → 0⁺` (perturbation) limits. -/
 lemma sandwichedRenyiDiv_continuousWithinAt_lt
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {ρ₀ σ₀ : L ℋ}
    (hρ₀ : 0 ≤ ρ₀) (hσ₀ : 0 ≤ σ₀)
    (hQ : (sandwichedQuasi α ρ₀ σ₀).re ≠ 0) (hTr : (Tr ρ₀).re ≠ 0) :
    ContinuousWithinAt (fun p : L ℋ × L ℋ => sandwichedRenyiDiv α p.1 p.2)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) (ρ₀, σ₀) := by
  have hcont := sandwichedQuasi_re_continuousOn_nonneg (ℋ := ℋ) hα0 hα1.le
  have hQc : ContinuousWithinAt (fun p : L ℋ × L ℋ => (sandwichedQuasi α p.1 p.2).re)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) (ρ₀, σ₀) :=
    hcont (ρ₀, σ₀) ⟨hρ₀, hσ₀⟩
  have h_trace_cont : Continuous (fun A : L ℋ => Tr A) :=
    LinearMap.continuous_of_finiteDimensional _
  have hTc : ContinuousWithinAt (fun p : L ℋ × L ℋ => (Tr p.1).re)
      ({A : L ℋ | 0 ≤ A} ×ˢ {A : L ℋ | 0 ≤ A}) (ρ₀, σ₀) :=
    (Complex.continuous_re.comp (h_trace_cont.comp continuous_fst)).continuousWithinAt
  have hRatio := hQc.div hTc hTr
  have h_div_ne : (sandwichedQuasi α ρ₀ σ₀).re / (Tr ρ₀).re ≠ 0 := div_ne_zero hQ hTr
  have hLog := (Real.continuousAt_log h_div_ne).tendsto.comp hRatio
  exact hLog.const_mul (1 / (α - 1))

/-! ### Boundary continuity of `sandwichedRenyiDiv` along the perturbation path -/

/-! #### Eigenvector formulas for the continuous functional calculus -/

/-- Natural-power eigenvector formula: `A v = c • v ⟹ Aⁿ v = cⁿ • v`. -/
 lemma pow_apply_of_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} {v : ℋ} {c : ℂ} (hv : A v = c • v) :
    ∀ n : ℕ, (A ^ n) v = c ^ n • v
  | 0 => by rw [pow_zero, Module.End.one_apply, pow_zero, one_smul]
  | n + 1 => by
    rw [pow_succ, Module.End.mul_apply, hv, LinearMap.map_smul,
        pow_apply_of_eigenvector hv n, smul_smul]
    congr 1
    rw [← pow_succ']

/-- Real-polynomial eigenvector formula: `A v = (c:ℂ) • v ⟹ (aeval A p) v = (p.eval c) • v`. -/
 lemma aeval_apply_of_eigenvector_real
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} {v : ℋ} {c : ℝ} (hv : A v = ((c : ℝ) : ℂ) • v) (p : Polynomial ℝ) :
    (Polynomial.aeval A p) v = ((p.eval c : ℝ) : ℂ) • v := by
  induction p using Polynomial.induction_on with
  | C r =>
    rw [Polynomial.aeval_C, Polynomial.eval_C]
    rw [show ((algebraMap ℝ (L ℋ)) r : L ℋ) = ((r : ℝ) : ℂ) • (1 : L ℋ) from by
      rw [show ((r : ℝ) : ℂ) • (1 : L ℋ) = (algebraMap ℂ (L ℋ)) ((r : ℝ) : ℂ) from
        (Algebra.algebraMap_eq_smul_one ((r : ℝ) : ℂ)).symm]
      rfl]
    rw [LinearMap.smul_apply, Module.End.one_apply]
  | add p q hp hq =>
    rw [map_add, Polynomial.eval_add, LinearMap.add_apply, hp, hq,
        Complex.ofReal_add, add_smul]
  | monomial n r _ =>
    rw [map_mul, Polynomial.aeval_C, map_pow, Polynomial.aeval_X,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
        Complex.ofReal_mul, Complex.ofReal_pow]
    rw [show ((algebraMap ℝ (L ℋ)) r : L ℋ) = ((r : ℝ) : ℂ) • (1 : L ℋ) from by
      rw [show ((r : ℝ) : ℂ) • (1 : L ℋ) = (algebraMap ℂ (L ℋ)) ((r : ℝ) : ℂ) from
        (Algebra.algebraMap_eq_smul_one ((r : ℝ) : ℂ)).symm]
      rfl]
    rw [smul_mul_assoc, one_mul, LinearMap.smul_apply,
        _root_.SandwichedRenyiRelativeEntropy.pow_apply_of_eigenvector hv (n + 1), smul_smul]

/-- `spectrum ℝ A` is finite for `A : L ℋ` (finite dimension). -/
 lemma spectrum_real_finite {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (A : L ℋ) :
    (spectrum ℝ A).Finite := by
  rw [← spectrum.preimage_algebraMap ℂ]
  exact (Module.End.finite_spectrum A).preimage
    (FaithfulSMul.algebraMap_injective ℝ ℂ).injOn

/-- **CFC on an eigenvector (real version).** If `A` is self-adjoint, `A v = μ • v`, and
    `μ ∈ spectrum ℝ A`, then `cfc f A v = f(μ) • v`. Proof by Lagrange interpolation:
    a polynomial `q` agreeing with `f` on the (finite) spectrum gives `cfc f A = aeval A q`,
    and `aeval A q v = q(μ) • v = f(μ) • v`. -/
lemma cfc_real_apply_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : IsSelfAdjoint A) (f : ℝ → ℝ)
    {v : ℋ} {μ : ℝ} (hv : A v = (μ : ℂ) • v) (hμ : μ ∈ spectrum ℝ A) :
    cfc f A v = ((f μ : ℝ) : ℂ) • v := by
  classical
  set S : Finset ℝ := (_root_.SandwichedRenyiRelativeEntropy.spectrum_real_finite A).toFinset with hS
  set q : Polynomial ℝ := Lagrange.interpolate S id f with hq
  have hInj : Set.InjOn (id : ℝ → ℝ) (S : Set ℝ) := Function.injective_id.injOn
  have hEvalNode : ∀ x ∈ S, q.eval x = f x := by
    intro x hx
    have := Lagrange.eval_interpolate_at_node (r := f) (v := id) hInj hx
    simpa using this
  have hEqOn : (spectrum ℝ A).EqOn f (fun x => q.eval x) := by
    intro x hx
    have hxS : x ∈ S := by rw [hS, Set.Finite.mem_toFinset]; exact hx
    exact (hEvalNode x hxS).symm
  have h1 : cfc f A = cfc (fun x => q.eval x) A := cfc_congr hEqOn
  have h2 : cfc (fun x => q.eval x) A = Polynomial.aeval A q := cfc_polynomial q A
  have hμS : μ ∈ S := by rw [hS, Set.Finite.mem_toFinset]; exact hμ
  rw [h1, h2, _root_.SandwichedRenyiRelativeEntropy.aeval_apply_of_eigenvector_real hv q, hEvalNode μ hμS]

/-- `CFC.rpow A y` on an eigenvector. -/
 lemma rpow_apply_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) (y : ℝ)
    {v : ℋ} {μ : ℝ} (hv : A v = (μ : ℂ) • v) (hμ : μ ∈ spectrum ℝ A) :
    CFC.rpow A y v = ((μ ^ y : ℝ) : ℂ) • v := by
  have hsa : IsSelfAdjoint A := (LinearMap.nonneg_iff_isPositive A).mp hA |>.isSelfAdjoint
  have heq : CFC.rpow A y = cfc (fun x : ℝ => x ^ y) A := by
    rw [CFC.rpow_eq_pow]; exact CFC.rpow_eq_cfc_real (ha := hA)
  rw [heq]
  exact cfc_real_apply_eigenvector hsa (fun x => x ^ y) hv hμ

/-- A real eigenvalue (with nonzero eigenvector) lies in `spectrum ℝ A`. -/
lemma mem_spectrum_real_of_eigenvector
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} {v : ℋ} {μ : ℝ} (hv0 : v ≠ 0) (hv : A v = (μ : ℂ) • v) :
    μ ∈ spectrum ℝ A := by
  have hev : Module.End.HasEigenvalue A (μ : ℂ) := by
    refine Module.End.hasEigenvalue_of_hasEigenvector ⟨?_, hv0⟩
    rw [Module.End.mem_eigenspace_iff]; exact hv
  have hmem : (μ : ℂ) ∈ spectrum ℂ A := hev.mem_spectrum
  rw [← spectrum.preimage_algebraMap ℂ] at *
  simpa using hmem

/-- `v ↦ outer_product u v` as a bundled (continuous) linear map. -/
 noncomputable def outerL {ℋ : Type u} [Qudit ℋ] (u : ℋ) : ℋ →ₗ[ℂ] L ℋ where
  toFun v := outer_product u v
  map_add' v w := by ext x; simp [_root_.SandwichedRenyiRelativeEntropy.outer_product_apply, smul_add]
  map_smul' c v := by
    ext x
    simp only [_root_.SandwichedRenyiRelativeEntropy.outer_product_apply, LinearMap.smul_apply, RingHom.id_apply]
    rw [smul_comm]

 lemma continuous_outerL {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (u : ℋ) :
    Continuous (fun v : ℋ => outer_product u v) :=
  (_root_.SandwichedRenyiRelativeEntropy.outerL u).continuous_of_finiteDimensional

/-- **Operator convergence under `suppLE` (α > 1).**
    `(σ+εI)^β (ρ+εI) (σ+εI)^β → σ^β ρ σ^β` as `ε → 0⁺`, where `β = (1-α)/(2α) < 0`.
    The pseudo-inverse blow-up of `(σ+εI)^β` on `ker σ` is killed because `ρ` vanishes
    there (`suppLE`); the residual `εI`-contribution on `ker σ` scales as `ε^{1/α} → 0`. -/
 lemma rpow_conj_tendsto_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α) {ρ σ : L ℋ}
    (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hsupp : suppLE ρ σ) :
    Filter.Tendsto
      (fun ε : ℝ => CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) ((1-α)/(2*α)) * (ρ + (ε:ℂ)•(1:L ℋ))
        * CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) ((1-α)/(2*α)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (CFC.rpow σ ((1-α)/(2*α)) * ρ * CFC.rpow σ ((1-α)/(2*α)))) := by
  classical
  set β : ℝ := (1-α)/(2*α) with hβ
  have hαpos : 0 < α := by linarith
  have hβneg : β < 0 := by
    rw [hβ]; apply div_neg_of_neg_of_pos (by linarith) (by positivity)
  have h2β : (1:ℝ) + 2*β = 1/α := by rw [hβ]; field_simp; ring
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
  have h_ker : ∀ k, eig k = 0 → ρ (b k) = 0 := by
    intro k hk
    have hσbk : σ (b k) = 0 := by rw [h_eig_apply k, hk]; simp
    exact hsupp (LinearMap.mem_ker.mpr hσbk)
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
  have hS0rho : ∀ i, CFC.rpow σ β (ρ (b i))
      = ∑ j, ((((eig j)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j := by
    intro i
    conv_lhs => rw [show ρ (b i) = ∑ j, inner ℂ (b j) (ρ (b i)) • b j from (b.sum_repr' (ρ (b i))).symm]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, hS0b j, smul_smul]
    congr 1; ring
  have hM0 : ∀ i, (CFC.rpow σ β * ρ * CFC.rpow σ β) (b i)
      = ∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j := by
    intro i
    rw [Module.End.mul_apply, Module.End.mul_apply, hS0b i, map_smul, map_smul, hS0rho i,
        Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    congr 1
    push_cast; ring
  have hMε : ∀ (ε : ℝ), 0 < ε → ∀ i,
      (CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β * (ρ + (ε:ℂ)•(1:L ℋ)) * CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β) (b i)
      = (∑ j, ((((eig i+ε)^β * (eig j+ε)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j)
        + (((ε * ((eig i+ε)^β)^2 : ℝ)):ℂ) • b i := by
    intro ε hε i
    have hε1_nn : (0:L ℋ) ≤ (ε:ℂ)•(1:L ℋ) :=
      smul_nonneg (Complex.zero_le_real.mpr hε.le) zero_le_one
    have hσε_nn : (0:L ℋ) ≤ σ + (ε:ℂ)•(1:L ℋ) := add_nonneg hσ hε1_nn
    have hσε_app : ∀ k, (σ + (ε:ℂ)•(1:L ℋ)) (b k) = ((eig k + ε : ℝ):ℂ) • b k := by
      intro k
      rw [LinearMap.add_apply, h_eig_apply k, LinearMap.smul_apply, Module.End.one_apply]
      rw [← add_smul]; push_cast; ring_nf
    have hσε_spec : ∀ k, (eig k + ε) ∈ spectrum ℝ (σ + (ε:ℂ)•(1:L ℋ)) :=
      fun k => mem_spectrum_real_of_eigenvector (hb_ne k) (hσε_app k)
    have hSb : ∀ k, CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β (b k) = (((eig k+ε)^β : ℝ):ℂ) • b k :=
      fun k => _root_.SandwichedRenyiRelativeEntropy.rpow_apply_eigenvector hσε_nn β (hσε_app k) (hσε_spec k)
    have hSrho : CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β (ρ (b i))
        = ∑ j, ((((eig j+ε)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j := by
      conv_lhs => rw [show ρ (b i) = ∑ j, inner ℂ (b j) (ρ (b i)) • b j from (b.sum_repr' (ρ (b i))).symm]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, hSb j, smul_smul]
      congr 1; ring
    rw [Module.End.mul_apply, Module.End.mul_apply, hSb i, map_smul, map_smul,
        LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_smul,
        hSrho, hSb i, smul_add, Finset.smul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul]
      congr 1
      push_cast; ring
    · rw [smul_smul, smul_smul]
      congr 1
      push_cast; ring
  have hrpow_tendsto : ∀ k, 0 < eig k →
      Filter.Tendsto (fun ε : ℝ => (eig k + ε)^β) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((eig k)^β)) := by
    intro k hk
    have h_add : Filter.Tendsto (fun ε : ℝ => eig k + ε) (nhdsWithin 0 (Set.Ioi 0)) (nhds (eig k)) := by
      have hcont : Continuous (fun ε : ℝ => eig k + ε) := by fun_prop
      have h0 : Filter.Tendsto (fun ε : ℝ => eig k + ε) (nhds 0) (nhds (eig k)) := by
        simpa using hcont.tendsto (0:ℝ)
      exact h0.mono_left nhdsWithin_le_nhds
    exact ((Real.continuousAt_rpow_const (eig k) β (Or.inl (ne_of_gt hk))).tendsto).comp h_add
  have hextra : ∀ i, Filter.Tendsto (fun ε : ℝ => (((ε * ((eig i+ε)^β)^2 : ℝ)) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro i
    have hα_inv_pos : (0:ℝ) < 1/α := one_div_pos.mpr hαpos
    have hg : Filter.Tendsto (fun ε : ℝ => ε ^ (1/α)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hc := (Real.continuousAt_rpow_const 0 (1/α) (Or.inr hα_inv_pos.le)).tendsto
      rw [Real.zero_rpow (ne_of_gt hα_inv_pos)] at hc
      exact hc.mono_left nhdsWithin_le_nhds
    have hreal : Filter.Tendsto (fun ε : ℝ => ε * ((eig i+ε)^β)^2) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      apply squeeze_zero' (f := fun ε => ε * ((eig i+ε)^β)^2) (g := fun ε => ε ^ (1/α))
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        exact mul_nonneg hε.le (sq_nonneg _)
      · filter_upwards [self_mem_nhdsWithin] with ε hε
        have hεpos : (0:ℝ) < ε := hε
        have hbase_nn : (0:ℝ) ≤ eig i + ε := add_nonneg (h_eig_nn i) hεpos.le
        have hsq : ((eig i+ε)^β)^2 = (eig i+ε)^(2*β) := by
          rw [← Real.rpow_natCast ((eig i+ε)^β) 2, ← Real.rpow_mul hbase_nn]
          ring_nf
        rw [hsq]
        have hle : (eig i+ε)^(2*β) ≤ ε^(2*β) :=
          Real.rpow_le_rpow_of_nonpos hεpos (by linarith [h_eig_nn i]) (by linarith)
        calc ε * (eig i+ε)^(2*β) ≤ ε * ε^(2*β) :=
              mul_le_mul_of_nonneg_left hle hεpos.le
          _ = ε^(1+2*β) := by rw [Real.rpow_add hεpos, Real.rpow_one]
          _ = ε^(1/α) := by rw [h2β]
      · exact hg
    have hcomp := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hreal
    simpa only [Function.comp_def, Complex.ofReal_zero] using hcomp
  have key : ∀ i, Filter.Tendsto
      (fun ε : ℝ => (CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β * (ρ + (ε:ℂ)•(1:L ℋ)) * CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β) (b i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((CFC.rpow σ β * ρ * CFC.rpow σ β) (b i))) := by
    intro i
    rw [hM0 i]
    have hEq : (fun ε : ℝ => (CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β * (ρ + (ε:ℂ)•(1:L ℋ)) * CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β) (b i))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun ε => (∑ j, ((((eig i+ε)^β * (eig j+ε)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j)
          + (((ε * ((eig i+ε)^β)^2 : ℝ)):ℂ) • b i) := by
      filter_upwards [self_mem_nhdsWithin] with ε hε
      exact hMε ε hε i
    refine Filter.Tendsto.congr' hEq.symm ?_
    rw [show (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j)
        = (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (ρ (b i))) • b j) + (0:ℋ) from
        (add_zero _).symm]
    apply Filter.Tendsto.add
    · apply tendsto_finset_sum
      intro j _
      by_cases hzero : eig i = 0 ∨ eig j = 0
      · have hin0 := h_supp_zero i j hzero
        rw [hin0]
        simp only [mul_zero, zero_smul]
        exact tendsto_const_nhds
      · push_neg at hzero
        obtain ⟨hi, hj⟩ := hzero
        have hi' : 0 < eig i := lt_of_le_of_ne (h_eig_nn i) (Ne.symm hi)
        have hj' : 0 < eig j := lt_of_le_of_ne (h_eig_nn j) (Ne.symm hj)
        have hsc : Filter.Tendsto (fun ε : ℝ => ((((eig i+ε)^β * (eig j+ε)^β : ℝ)):ℂ) * inner ℂ (b j) (ρ (b i)))
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (((((eig i)^β * (eig j)^β : ℝ)):ℂ) * inner ℂ (b j) (ρ (b i)))) := by
          apply Filter.Tendsto.mul_const
          have hr : Filter.Tendsto (fun ε : ℝ => ((eig i+ε)^β * (eig j+ε)^β : ℝ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds ((eig i)^β * (eig j)^β)) :=
            (hrpow_tendsto i hi').mul (hrpow_tendsto j hj')
          exact (Complex.continuous_ofReal.tendsto _).comp hr
        exact hsc.smul_const (b j)
    · rw [show (0:ℋ) = (0:ℂ) • b i from (zero_smul ℂ (b i)).symm]
      exact (hextra i).smul_const (b i)
  have hrecon0 : (CFC.rpow σ β * ρ * CFC.rpow σ β)
      = ∑ i, outer_product (b i) ((CFC.rpow σ β * ρ * CFC.rpow σ β) (b i)) :=
    linearMap_eq_sum_outer_product b _
  have hfun : (fun ε : ℝ => CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β * (ρ + (ε:ℂ)•(1:L ℋ)) * CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β)
      = (fun ε : ℝ => ∑ i, outer_product (b i)
          ((CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β * (ρ + (ε:ℂ)•(1:L ℋ)) * CFC.rpow (σ + (ε:ℂ)•(1:L ℋ)) β) (b i))) :=
    funext fun ε => linearMap_eq_sum_outer_product b _
  rw [hrecon0, hfun]
  apply tendsto_finset_sum
  intro i _
  exact ((_root_.SandwichedRenyiRelativeEntropy.continuous_outerL (b i)).tendsto _).comp (key i)
end SandwichedRenyiRelativeEntropy


