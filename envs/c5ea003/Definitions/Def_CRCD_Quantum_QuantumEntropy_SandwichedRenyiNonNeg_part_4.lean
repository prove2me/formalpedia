-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_4
-- name    : CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_4
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T01:42:08.129042+00:00
-- url     : https://prove2.me/theorems/22078376-bee3-4349-8478-b8ad6801f1ec
-- title:
--   Faithful-path convergence and finite-valued Rényi data processing
-- statement:
--   On a nonzero finite-dimensional complex Hilbert space, let $A,B\ge0$, $\ker A\subseteq\ker B$, $c_A>0$, $c_B\ge0$, $\alpha>1$ and $\beta=(1-\alpha)/(2\alpha)$. Set $A_\lambda=(1-\lambda)A+\lambda c_AI$ and $B_\lambda=(1-\lambda)B+\lambda c_BI$. The part proves
--   $$
--   A_\lambda^\beta B_\lambda A_\lambda^\beta\longrightarrow A^\beta BA^\beta\quad(\lambda\to0^+).
--   $$
--   For a CPTP map $\Phi:L(H)\to L(K)$ between nonzero finite-dimensional spaces, its faithful approximations therefore satisfy
--   $$
--   D_\alpha(F_\lambda(\rho)\Vert F_\lambda(\sigma))\longrightarrow
--   D_\alpha(\Phi(\rho)\Vert\Phi(\sigma))
--   $$
--   for $\alpha>1$, $\rho,\sigma\ge0$, both nonzero, and the explicit output support premise $\ker\Phi(\sigma)\subseteq\ker\Phi(\rho)$, with $\lambda\in(0,1]$ tending to zero.
--
--   It also proves $D_\alpha(\Phi(\rho)\Vert\Phi(\sigma))\le D_\alpha(\rho\Vert\sigma)$ in two finite-valued regimes. Above one, the supplied premises are positive semidefinite inputs, $\rho\ne0$, and both input and output support inclusions. For $1/2\le\alpha<1$, they are positive semidefinite inputs, $\rho\ne0$, and nonzero real quasi-entropies at both the input and output pairs. These auxiliary statements concern the real trace-normalized natural-logarithmic divergence; they retain their support/nonvanishing premises rather than asserting the unrestricted extended-real result of the next part.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedRenyiNonNeg.lean#L1777-L2284

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
import Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_3
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





























/-! ### Helpers for the `α < 1` main-theorem case -/











/-! ### Real-valued monotonicity (used in the main theorem) -/







/-- **Operator convergence along the faithful path** (`α > 1`). With
    `Pσ λ := (1−λ)•A + (λ·cσ)•1` and `Pρ λ := (1−λ)•B + (λ·cρ)•1` (`A = Eσ`, `B = Eρ`,
    `cσ > 0`, `cρ ≥ 0`), `Pσ^β Pρ Pσ^β → A^β B A^β` as `λ → 0⁺`. The depolarizing shift
    `(λ·cσ)•1` commutes with `A`, so the pseudo-inverse blow-up on `ker A` is killed by
    `suppLE B A`; the residual `ker A`-contribution scales as `λ^{1/α} → 0`. -/
 lemma rpow_conj_tendsto_faithful
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {α : ℝ} (hα_gt : 1 < α) {A B : L ℋ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hsupp : suppLE B A)
    {cσ cρ : ℝ} (hcσ : 0 < cσ) (hcρ : 0 ≤ cρ) :
    Filter.Tendsto
      (fun lam : ℝ =>
        CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) ((1-α)/(2*α))
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) ((1-α)/(2*α)))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (CFC.rpow A ((1-α)/(2*α)) * B * CFC.rpow A ((1-α)/(2*α)))) := by
  classical
  set β : ℝ := (1-α)/(2*α) with hβ
  have hαpos : 0 < α := by linarith
  have hβneg : β < 0 := by
    rw [hβ]; apply div_neg_of_neg_of_pos (by linarith) (by positivity)
  have h2β : (1:ℝ) + 2*β = 1/α := by rw [hβ]; field_simp; ring
  have hα_inv_pos : (0:ℝ) < 1/α := one_div_pos.mpr hαpos
  set n := Module.finrank ℂ ℋ with hn_def
  have hn : Module.finrank ℂ ℋ = n := rfl
  have hA_pos : A.IsPositive := (LinearMap.nonneg_iff_isPositive A).mp hA
  have hA_sym : A.IsSymmetric := hA_pos.isSymmetric
  have hB_sym : B.IsSymmetric := ((LinearMap.nonneg_iff_isPositive B).mp hB).isSymmetric
  set b := hA_sym.eigenvectorBasis hn with hb
  set eig := hA_sym.eigenvalues hn with heig
  have h_eig_nn : ∀ i, 0 ≤ eig i := fun i => hA_pos.nonneg_eigenvalues hn i
  have h_eig_apply : ∀ i, A (b i) = ((eig i : ℝ):ℂ) • b i := hA_sym.apply_eigenvectorBasis hn
  have hb_ne : ∀ i, b i ≠ 0 := fun i => b.orthonormal.ne_zero i
  have h_ker : ∀ k, eig k = 0 → B (b k) = 0 := by
    intro k hk
    exact hsupp (LinearMap.mem_ker.mpr (by rw [h_eig_apply k, hk]; simp))
  have h_supp_zero : ∀ i j, (eig i = 0 ∨ eig j = 0) → inner ℂ (b j) (B (b i)) = (0:ℂ) := by
    intro i j hij
    rcases hij with hi | hj
    · rw [h_ker i hi]; simp
    · rw [show inner ℂ (b j) (B (b i)) = inner ℂ (B (b j)) (b i) from (hB_sym (b j) (b i)).symm,
          h_ker j hj]; simp
  -- eigenvalue of the perturbed operator `Pσ λ`.
  set ν : ℝ → Fin n → ℝ := fun lam i => (1-lam)*eig i + lam*cσ with hν
  have hPσ_app : ∀ (lam : ℝ) k,
      (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) (b k) = ((ν lam k : ℝ):ℂ) • b k := by
    intro lam k
    rw [LinearMap.add_apply, LinearMap.smul_apply, h_eig_apply k, LinearMap.smul_apply,
        Module.End.one_apply, smul_smul, ← add_smul, hν]
    push_cast; ring_nf
  have hν_pos : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ k, 0 < ν lam k := by
    intro lam hlam0 hlam1 k
    have h1 : 0 ≤ (1-lam)*eig k := mul_nonneg (by linarith) (h_eig_nn k)
    have h2 : 0 < lam*cσ := mul_pos hlam0 hcσ
    rw [hν]; linarith
  have hν_le : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ k, lam*cσ ≤ ν lam k := by
    intro lam hlam0 hlam1 k
    have h1 : 0 ≤ (1-lam)*eig k := mul_nonneg (by linarith) (h_eig_nn k)
    rw [hν]; linarith
  -- `A^β (b i) = (eig i)^β • b i`.
  have hspec0 : ∀ i, eig i ∈ spectrum ℝ A :=
    fun i => mem_spectrum_real_of_eigenvector (hb_ne i) (h_eig_apply i)
  have hS0b : ∀ i, CFC.rpow A β (b i) = (((eig i)^β : ℝ):ℂ) • b i :=
    fun i => _root_.SandwichedRenyiRelativeEntropy.rpow_apply_eigenvector hA β (h_eig_apply i) (hspec0 i)
  have hS0rho : ∀ i, CFC.rpow A β (B (b i))
      = ∑ j, ((((eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j := by
    intro i
    conv_lhs => rw [show B (b i) = ∑ j, inner ℂ (b j) (B (b i)) • b j from (b.sum_repr' (B (b i))).symm]
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [map_smul, hS0b j, smul_smul]
    congr 1; ring
  have hM0 : ∀ i, (CFC.rpow A β * B * CFC.rpow A β) (b i)
      = ∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j := by
    intro i
    rw [Module.End.mul_apply, Module.End.mul_apply, hS0b i, map_smul, map_smul, hS0rho i,
        Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [smul_smul]
    congr 1
    push_cast; ring
  -- per-λ formula for `Pσ^β Pρ Pσ^β (b i)`.
  have hMlam : ∀ (lam : ℝ), 0 < lam → lam ≤ 1 → ∀ i,
      (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
        * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
        * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β) (b i)
      = (∑ j, (((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
            * inner ℂ (b j) (B (b i))) • b j)
        + (((lam*cρ * ((ν lam i)^β)^2 : ℝ)):ℂ) • b i := by
    intro lam hlam0 hlam1 i
    set Aε : L ℋ := ((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ) with hAε
    have hAε_nn : (0:L ℋ) ≤ Aε := by
      rw [hAε]
      exact add_nonneg (smul_nonneg (Complex.zero_le_real.mpr (by linarith)) hA)
        (smul_nonneg (Complex.zero_le_real.mpr (by positivity)) zero_le_one)
    have hAε_app : ∀ k, Aε (b k) = ((ν lam k : ℝ):ℂ) • b k := hPσ_app lam
    have hAε_spec : ∀ k, ν lam k ∈ spectrum ℝ Aε :=
      fun k => mem_spectrum_real_of_eigenvector (hb_ne k) (hAε_app k)
    have hSb : ∀ k, CFC.rpow Aε β (b k) = (((ν lam k)^β : ℝ):ℂ) • b k :=
      fun k => _root_.SandwichedRenyiRelativeEntropy.rpow_apply_eigenvector hAε_nn β (hAε_app k) (hAε_spec k)
    -- expand `(Pρ λ)(b i) = (1-λ)•B(b i) + (λcρ)•b i`.
    have hPρ_app : (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ)) (b i)
        = ((1-lam:ℝ):ℂ) • B (b i) + ((lam*cρ:ℝ):ℂ) • b i := by
      rw [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.smul_apply, Module.End.one_apply]
    have hSrho : CFC.rpow Aε β (B (b i))
        = ∑ j, ((((ν lam j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j := by
      conv_lhs => rw [show B (b i) = ∑ j, inner ℂ (b j) (B (b i)) • b j from (b.sum_repr' (B (b i))).symm]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, hSb j, smul_smul]
      congr 1; ring
    rw [Module.End.mul_apply, Module.End.mul_apply, hSb i, map_smul, map_smul, hPρ_app,
        map_add, map_smul, map_smul, hSrho, hSb i, smul_add]
    congr 1
    · rw [smul_smul, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [smul_smul]
      congr 1
      push_cast; ring
    · rw [smul_smul, smul_smul]
      congr 1
      push_cast; ring
  -- `ν lam k → eig k` as `λ → 0⁺`.
  have hν_tendsto : ∀ k, Filter.Tendsto (fun lam : ℝ => ν lam k)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (eig k)) := by
    intro k
    have hcont : Continuous (fun lam : ℝ => ν lam k) := by rw [hν]; fun_prop
    have h0 : Filter.Tendsto (fun lam : ℝ => ν lam k) (nhds 0) (nhds (ν 0 k)) := hcont.tendsto 0
    have : ν 0 k = eig k := by rw [hν]; ring
    rw [this] at h0
    exact h0.mono_left nhdsWithin_le_nhds
  have hrpow_tendsto : ∀ k, 0 < eig k →
      Filter.Tendsto (fun lam : ℝ => (ν lam k)^β) (nhdsWithin 0 (Set.Ioi 0)) (nhds ((eig k)^β)) :=
    fun k hk => ((Real.continuousAt_rpow_const (eig k) β (Or.inl (ne_of_gt hk))).tendsto).comp
      (hν_tendsto k)
  -- extra-term scalar `λ·cρ·(ν λ i)^{2β} → 0`.
  have hextra : ∀ i, Filter.Tendsto (fun lam : ℝ => (((lam*cρ * ((ν lam i)^β)^2 : ℝ)) : ℂ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    intro i
    have hg : Filter.Tendsto (fun lam : ℝ => cρ * cσ^(2*β) * lam ^ (1/α))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have hgc : Filter.Tendsto (fun lam : ℝ => lam ^ (1/α))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have h0 := (Real.continuousAt_rpow_const 0 (1/α) (Or.inr hα_inv_pos.le)).tendsto
        rw [Real.zero_rpow (ne_of_gt hα_inv_pos)] at h0
        exact h0.mono_left nhdsWithin_le_nhds
      have := hgc.const_mul (cρ * cσ^(2*β))
      simpa using this
    have hIio : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
    have hreal : Filter.Tendsto (fun lam : ℝ => lam*cρ * ((ν lam i)^β)^2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      apply squeeze_zero' (f := fun lam => lam*cρ * ((ν lam i)^β)^2)
        (g := fun lam => cρ * cσ^(2*β) * lam ^ (1/α))
      · filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
        have hlam0 : (0:ℝ) < lam := hlam
        exact mul_nonneg (mul_nonneg hlam0.le hcρ) (sq_nonneg _)
      · filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
        have hlam0 : (0:ℝ) < lam := hlam
        have hlam1' : lam ≤ 1 := le_of_lt hlam1
        have hνpos : 0 < ν lam i := hν_pos lam hlam0 hlam1' i
        have hsq : ((ν lam i)^β)^2 = (ν lam i)^(2*β) := by
          rw [← Real.rpow_natCast ((ν lam i)^β) 2, ← Real.rpow_mul hνpos.le]
          ring_nf
        rw [hsq]
        have hlamcσ : 0 < lam*cσ := mul_pos hlam0 hcσ
        have hle : (ν lam i)^(2*β) ≤ (lam*cσ)^(2*β) :=
          Real.rpow_le_rpow_of_nonpos hlamcσ (hν_le lam hlam0 hlam1' i) (by linarith)
        have hlampow : lam * lam^(2*β) = lam ^ (1/α) := by
          rw [← h2β, Real.rpow_add hlam0, Real.rpow_one]
        calc lam*cρ * (ν lam i)^(2*β) ≤ lam*cρ * (lam*cσ)^(2*β) :=
              mul_le_mul_of_nonneg_left hle (mul_nonneg hlam0.le hcρ)
          _ = cρ * cσ^(2*β) * lam ^ (1/α) := by
                rw [Real.mul_rpow hlam0.le hcσ.le, ← hlampow]; ring
      · exact hg
    have hcomp := (Complex.continuous_ofReal.tendsto (0:ℝ)).comp hreal
    simpa only [Function.comp_def, Complex.ofReal_zero] using hcomp
  -- per-i vector convergence.
  have key : ∀ i, Filter.Tendsto
      (fun lam : ℝ =>
        (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β) (b i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds ((CFC.rpow A β * B * CFC.rpow A β) (b i))) := by
    intro i
    rw [hM0 i]
    have hIio : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
      nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
    have hEq : (fun lam : ℝ =>
        (CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β) (b i))
        =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun lam => (∑ j, (((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
            * inner ℂ (b j) (B (b i))) • b j)
          + (((lam*cρ * ((ν lam i)^β)^2 : ℝ)):ℂ) • b i) := by
      filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
      exact hMlam lam hlam (le_of_lt hlam1) i
    refine Filter.Tendsto.congr' hEq.symm ?_
    rw [show (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j)
        = (∑ j, ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i))) • b j) + (0:ℋ) from
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
        have hsc : Filter.Tendsto
            (fun lam : ℝ => ((1-lam : ℝ):ℂ) * (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ)
              * inner ℂ (b j) (B (b i)))
            (nhdsWithin 0 (Set.Ioi 0))
            (nhds ((((eig i)^β * (eig j)^β : ℝ):ℂ) * inner ℂ (b j) (B (b i)))) := by
          have hone : Filter.Tendsto (fun lam : ℝ => ((1-lam : ℝ):ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
            have hc : Continuous (fun lam : ℝ => ((1-lam : ℝ):ℂ)) := by fun_prop
            have := hc.tendsto 0
            simpa using this.mono_left nhdsWithin_le_nhds
          have hr : Filter.Tendsto (fun lam : ℝ => (((ν lam i)^β * (ν lam j)^β : ℝ):ℂ))
              (nhdsWithin 0 (Set.Ioi 0)) (nhds ((((eig i)^β * (eig j)^β : ℝ)):ℂ)) :=
            (Complex.continuous_ofReal.tendsto _).comp ((hrpow_tendsto i hi').mul (hrpow_tendsto j hj'))
          have hprod := (hone.mul hr).mul_const (inner ℂ (b j) (B (b i)))
          simpa using hprod
        simpa using hsc.smul_const (b j)
    · rw [show (0:ℋ) = (0:ℂ) • b i from (zero_smul ℂ (b i)).symm]
      exact (hextra i).smul_const (b i)
  -- assemble via outer-product reconstruction.
  have hrecon0 : (CFC.rpow A β * B * CFC.rpow A β)
      = ∑ i, outer_product (b i) ((CFC.rpow A β * B * CFC.rpow A β) (b i)) :=
    linearMap_eq_sum_outer_product b _
  have hfun : (fun lam : ℝ =>
        CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
          * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
          * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β)
      = (fun lam : ℝ => ∑ i, outer_product (b i)
          ((CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β
            * (((1-lam:ℝ):ℂ)•B + ((lam*cρ:ℝ):ℂ)•(1:L ℋ))
            * CFC.rpow (((1-lam:ℝ):ℂ)•A + ((lam*cσ:ℝ):ℂ)•(1:L ℋ)) β) (b i))) :=
    funext fun lam => linearMap_eq_sum_outer_product b _
  rw [hrecon0, hfun]
  apply tendsto_finset_sum
  intro i _
  exact ((_root_.SandwichedRenyiRelativeEntropy.continuous_outerL (b i)).tendsto _).comp (key i)

/-- **`λ → 0⁺` boundary continuity along the faithful (depolarizing) path** (`α > 1`):
    `D_α(F_λρ ‖ F_λσ) → D_α(Eρ ‖ Eσ)`. The pseudo-inverse blow-up of `(F_λσ)^β` is killed by
    `suppLE (Eρ) (Eσ)` (the depolarizing perturbation commutes with `Eσ`). -/
 lemma sandwichedRenyiDiv_tendsto_faithful
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hσ0 : σ ≠ 0) (hρ0 : ρ ≠ 0)
    (hEsupp : suppLE (E.toFun ρ) (E.toFun σ)) :
    Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        sandwichedRenyiDiv α
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhds (sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ))) := by
  classical
  have hαpos : 0 < α := by linarith
  set β : ℝ := (1-α)/(2*α) with hβ
  set Eρ : L 𝒦 := E.toFun ρ with hEρdef
  set Eσ : L 𝒦 := E.toFun σ with hEσdef
  have hEρ_nn : (0:L 𝒦) ≤ Eρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ_nn : (0:L 𝒦) ≤ Eσ := map_nonneg E.toCompletelyPositiveMap hσ
  have hd_pos : 0 < (Module.finrank ℂ 𝒦 : ℝ) := by exact_mod_cast Module.finrank_pos
  set cσ : ℝ := (Tr σ).re / (Module.finrank ℂ 𝒦 : ℝ) with hcσ
  set cρ : ℝ := (Tr ρ).re / (Module.finrank ℂ 𝒦 : ℝ) with hcρ
  have hcσ_pos : 0 < cσ := div_pos (trace_re_pos_of_ne_zero hσ hσ0) hd_pos
  have hcρ_nn : 0 ≤ cρ := div_nonneg (le_of_lt (trace_re_pos_of_ne_zero hρ hρ0)) hd_pos.le
  have hEρ0 : Eρ ≠ 0 := by
    intro h
    have hz : (Tr Eρ).re = 0 := by rw [h]; simp
    rw [hEρdef, ← E.trace_map ρ] at hz
    exact (trace_re_pos_of_ne_zero hρ hρ0).ne' hz
  -- Operator convergence along the faithful path (in the target space `𝒦`).
  have hM := _root_.SandwichedRenyiRelativeEntropy.rpow_conj_tendsto_faithful (ℋ := 𝒦) hα_gt hEσ_nn hEρ_nn hEsupp hcσ_pos hcρ_nn
  -- Wrap to `sandwichedQuasi` via continuity of `X ↦ Tr (X^α)` on the non-negative cone.
  have hMnn : ∀ X Y : L 𝒦, 0 ≤ Y → (0:L 𝒦) ≤ CFC.rpow X β * Y * CFC.rpow X β :=
    fun X Y hY => conjugate_nonneg_of_nonneg hY CFC.rpow_nonneg
  have hcont : ContinuousWithinAt (fun X : L 𝒦 => Tr (CFC.rpow X α)) {X : L 𝒦 | 0 ≤ X}
      (CFC.rpow Eσ β * Eρ * CFC.rpow Eσ β) := by
    have h1 : ContinuousOn (fun X : L 𝒦 => CFC.rpow X α) {X : L 𝒦 | 0 ≤ X} :=
      _root_.QCProve2mePrivate.Quantum_QuantumEntropy_SandwichedRenyiNonNeg_rpow_continuousOn_nonneg (le_of_lt hαpos)
    have h2 : Continuous (fun A : L 𝒦 => Tr A) := LinearMap.continuous_of_finiteDimensional _
    exact (h2.comp_continuousOn h1).continuousWithinAt (hMnn Eσ Eρ hEρ_nn)
  have hIio : Set.Iio (1:ℝ) ∈ nhdsWithin (0:ℝ) (Set.Ioi 0) :=
    nhdsWithin_le_nhds (Iio_mem_nhds one_pos)
  have hMwithin : Filter.Tendsto
      (fun lam : ℝ => CFC.rpow (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1:L 𝒦)) β
        * (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))
        * CFC.rpow (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1:L 𝒦)) β)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin (CFC.rpow Eσ β * Eρ * CFC.rpow Eσ β) {X : L 𝒦 | 0 ≤ X}) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hM, ?_⟩
    filter_upwards [self_mem_nhdsWithin, hIio] with lam hlam hlam1
    have hlam0 : (0:ℝ) < lam := hlam
    have hlam1' : lam < 1 := hlam1
    have hPρ_nn : (0:L 𝒦) ≤ ((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦) :=
      add_nonneg (smul_nonneg (Complex.zero_le_real.mpr (by linarith)) hEρ_nn)
        (smul_nonneg (Complex.zero_le_real.mpr (mul_nonneg hlam0.le hcρ_nn)) zero_le_one)
    exact hMnn _ _ hPρ_nn
  have hQcx := Filter.Tendsto.comp hcont hMwithin
  -- `sandwichedRenyiDiv` tendsto over the real parameter `λ`.
  have hTr0 : (Tr Eρ).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hEρ_nn hEρ0)
  have hQ0 : (sandwichedQuasi α Eρ Eσ).re ≠ 0 :=
    _root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_re_ne_zero_of_suppLE hα_gt hEρ_nn hEσ_nn hEsupp hEρ0
  have hQre : Filter.Tendsto
      (fun lam : ℝ => (sandwichedQuasi α (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))
        (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1:L 𝒦))).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (sandwichedQuasi α Eρ Eσ).re) :=
    (Complex.continuous_re.tendsto _).comp hQcx
  have hTre : Filter.Tendsto
      (fun lam : ℝ => (Tr (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))).re)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Tr Eρ).re) := by
    have hform : ∀ lam : ℝ, (Tr (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))).re
        = (1-lam) * (Tr Eρ).re + (lam*cρ) * (Module.finrank ℂ 𝒦 : ℝ) := by
      intro lam
      rw [map_add, map_smul, map_smul, LinearMap.trace_one, smul_eq_mul, smul_eq_mul,
          Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.natCast_re]
    simp_rw [hform]
    have hcont : Continuous
        (fun lam : ℝ => (1-lam) * (Tr Eρ).re + (lam*cρ) * (Module.finrank ℂ 𝒦 : ℝ)) := by
      fun_prop
    have h2 := hcont.tendsto 0
    have h3 : (1-(0:ℝ)) * (Tr Eρ).re + (0*cρ) * (Module.finrank ℂ 𝒦 : ℝ) = (Tr Eρ).re := by ring
    rw [h3] at h2
    exact h2.mono_left nhdsWithin_le_nhds
  have hD : Filter.Tendsto
      (fun lam : ℝ => sandwichedRenyiDiv α (((1-lam:ℝ):ℂ)•Eρ + ((lam*cρ:ℝ):ℂ)•(1:L 𝒦))
        (((1-lam:ℝ):ℂ)•Eσ + ((lam*cσ:ℝ):ℂ)•(1:L 𝒦)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (sandwichedRenyiDiv α Eρ Eσ)) := by
    unfold sandwichedRenyiDiv
    have hRatio := Filter.Tendsto.div hQre hTre hTr0
    exact ((Real.continuousAt_log (div_ne_zero hQ0 hTr0)).tendsto.comp hRatio).const_mul _
  -- Transfer to the subtype filter; identify `F_λ.toFun` with the explicit perturbation.
  have hFeq : ∀ (X : L ℋ) (cX : ℝ), cX = (Tr X).re / (Module.finrank ℂ 𝒦 : ℝ) → 0 ≤ X →
      ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
        (faithfulApprox E l.val l.property.1.le l.property.2).toFun X
          = ((1-l.val:ℝ):ℂ)•E.toFun X + ((l.val*cX:ℝ):ℂ)•(1:L 𝒦) := by
    intro X cX hcX hX l
    have hTrX_re : Tr X = ((Tr X).re : ℂ) := by
      have h := ((LinearMap.nonneg_iff_isPositive X).mp hX).trace_nonneg
      rw [Complex.le_def] at h
      exact (Complex.ext rfl h.2.symm)
    change ((1-l.val:ℝ):ℂ)•E.toFun X + ((l.val:ℝ):ℂ)•((Tr X/(Module.finrank ℂ 𝒦:ℂ))•(1:L 𝒦)) = _
    rw [smul_smul]
    congr 2
    rw [hTrX_re, hcX]
    push_cast
    field_simp
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
  have htc : Filter.Tendsto (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhdsWithin 0 (Set.Ioi 0)) := Filter.tendsto_comap
  have hcomp := hD.comp htc
  refine hcomp.congr' ?_
  filter_upwards with l
  rw [Function.comp_apply, hFeq ρ cρ hcρ hρ l, hFeq σ cσ hcσ hσ l]

/-- **Real-valued monotonicity for `α > 1`** with the support condition and `ρ ≠ 0`.

    Mirrors the `α < 1` proof (`sandwichedRenyiDivNN_monotone_real_aux_lt`):

    1. **Faithful DPI per `λ`** (`step1`): for each `λ ∈ (0, 1]`, `F_λ` is faithful
       (`F_λ 1 ∈ pdSetLM`), and `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)` — obtained by taking
       `ε → 0⁺` in the perturbed PD inequality, with the LHS limit using PD-continuity
       (the path `F_λ(ρ+εI) = F_λρ + ε F_λ1` stays in `pdSetLM`) and the RHS limit using
       boundary continuity under `suppLE` (`sandwichedRenyiDiv_tendsto_of_suppLE`).
    2. **`λ → 0⁺`** (`step2`): `(F_λρ, F_λσ) → (Eρ, Eσ)` and `D_α(F_λρ ‖ F_λσ) →
       D_α(Eρ ‖ Eσ)` by boundary continuity along the faithful (depolarizing) path. -/
 lemma sandwichedRenyiDivNN_monotone_real_aux
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ} (hα_gt : 1 < α)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ)
    (hsupp : suppLE ρ σ) (hEsupp : suppLE (E.toFun ρ) (E.toFun σ)) (hρ0 : ρ ≠ 0) :
    sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  have hα_ge : (1 : ℝ) / 2 ≤ α := by linarith
  have hα0 : 0 < α := by linarith
  have hσ0 : σ ≠ 0 := by
    rintro rfl
    apply hρ0
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.zero_apply]
    exact LinearMap.mem_ker.mp (hsupp (LinearMap.mem_ker.mpr (by simp)))
  -- **Step 1**: faithful DPI for each `λ ∈ (0,1]`.
  have step1 : ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
      sandwichedRenyiDiv α
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ)
        ≤ sandwichedRenyiDiv α ρ σ := by
    rintro ⟨lam, hlam0, hlam1⟩
    exact _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_faithfulApprox_le_gt E hα_gt hρ hσ hρ0 hsupp hlam0 hlam1
  -- **Step 2**: `λ → 0⁺`, boundary continuity along the faithful path.
  haveI hNeBot : (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val)
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
  have step2 : Filter.Tendsto
      (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} =>
        sandwichedRenyiDiv α
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ))
      (Filter.comap (fun l : {l : ℝ // 0 < l ∧ l ≤ 1} => l.val) (nhdsWithin 0 (Set.Ioi 0)))
      (nhds (sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ))) :=
    _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_tendsto_faithful E hα_gt hρ hσ hσ0 hρ0 hEsupp
  exact le_of_tendsto step2 (Filter.Eventually.of_forall step1)

/-- Real-valued monotonicity for `α < 1`, in the non-orthogonal regime
    (`Q_α(ρ‖σ) ≠ 0` and `Q_α(Eρ‖Eσ) ≠ 0`).

    **Proof**: For each `λ ∈ (0,1]`, the faithful approximation `F_λ` satisfies
    `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)` — obtained by taking `ε → 0⁺` in the perturbed PD
    inequality `sandwichedRenyiDiv_monotone_nonneg_perturbed` (`F_λρ, F_λσ` are pd, so
    no support condition is needed and `Q_α > 0` automatically). Taking `λ → 0⁺`, the
    LHS converges to `D_α(Eρ ‖ Eσ)` by nonneg-cone continuity (`Q_α(Eρ‖Eσ) ≠ 0`). -/
 lemma sandwichedRenyiDivNN_monotone_real_aux_lt
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {α : ℝ}
    (hα_ge : (1 : ℝ) / 2 ≤ α) (hα_lt : α < 1)
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (hρ0 : ρ ≠ 0)
    (hQρσ : (sandwichedQuasi α ρ σ).re ≠ 0)
    (hQEρσ : (sandwichedQuasi α (E.toFun ρ) (E.toFun σ)).re ≠ 0) :
    sandwichedRenyiDiv α (E.toFun ρ) (E.toFun σ) ≤ sandwichedRenyiDiv α ρ σ := by
  have hα0 : 0 < α := by linarith
  have hEρ : (0 : L 𝒦) ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ : (0 : L 𝒦) ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
  have hTrρ : (Tr ρ).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hρ hρ0)
  have hEρ0 : E.toFun ρ ≠ 0 := by
    intro h
    have hz : (Tr (E.toFun ρ)).re = 0 := by rw [h]; simp
    rw [← E.trace_map ρ] at hz
    exact hTrρ hz
  have hTrEρ : (Tr (E.toFun ρ)).re ≠ 0 := ne_of_gt (trace_re_pos_of_ne_zero hEρ hEρ0)
  -- `Q_α(ρ‖σ) ≠ 0` forces `σ ≠ 0` (otherwise `σ^β = 0` and `Q = 0`).
  have hβne : (1 - α) / (2 * α) ≠ 0 := div_ne_zero (by linarith) (by positivity)
  have hσ0 : σ ≠ 0 := by
    intro h
    apply hQρσ
    rw [_root_.SandwichedRenyiRelativeEntropy.sandwichedQuasi_re_eq_zero_iff hα0 hρ hσ, h, CFC.zero_rpow hβne, zero_mul, mul_zero]
  -- **Step 1**: for each `λ ∈ (0,1]`, `D_α(F_λρ ‖ F_λσ) ≤ D_α(ρ‖σ)`.
  have step1 : ∀ (l : {l : ℝ // 0 < l ∧ l ≤ 1}),
      sandwichedRenyiDiv α
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun ρ)
          ((faithfulApprox E l.val l.property.1.le l.property.2).toFun σ)
        ≤ sandwichedRenyiDiv α ρ σ := by
    rintro ⟨lam, hlam0, hlam1⟩
    exact _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_faithfulApprox_le E hα_ge hα_lt hρ hσ hρ0 hσ0 hQρσ hlam0 hlam1
  -- **Step 2**: `λ → 0⁺`. `(F_λρ, F_λσ) → (Eρ, Eσ)` within the non-negative cone.
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
  have hcwa : ContinuousWithinAt (fun p : L 𝒦 × L 𝒦 => sandwichedRenyiDiv α p.1 p.2)
      ({A : L 𝒦 | 0 ≤ A} ×ˢ {A : L 𝒦 | 0 ≤ A}) (E.toFun ρ, E.toFun σ) :=
    _root_.SandwichedRenyiRelativeEntropy.sandwichedRenyiDiv_continuousWithinAt_lt hα0 hα_lt hEρ hEσ hQEρσ hTrEρ
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
  exact le_of_tendsto hlim (Filter.Eventually.of_forall step1)
end SandwichedRenyiRelativeEntropy


