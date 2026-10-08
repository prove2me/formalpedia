-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_1
-- name    : CRCD_Quantum_QuantumEntropy_SandwichedRenyiNonNeg_part_1
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T01:28:16.723809+00:00
-- url     : https://prove2.me/theorems/e88ceb08-e747-49e8-b5ce-1e203e0694c9
-- title:
--   Support-aware Rényi divergence and depolarizing channel approximations
-- statement:
--   On a nonzero finite-dimensional complex Hilbert space, define $\rho\preceq_{\mathrm{supp}}\sigma$ by $\ker\sigma\subseteq\ker\rho$. With $Q_\alpha$ and the trace-normalized natural-logarithmic real divergence $D_\alpha$ from the preceding parts, define an extended-real divergence by
--   $$
--   D^{\mathrm{NN}}_\alpha(\rho\Vert\sigma)=
--   \begin{cases}
--   +\infty,&\alpha>1\text{ and }\ker\sigma\nsubseteq\ker\rho,\\
--   +\infty,&\alpha<1,\ \rho\ne0,\ \operatorname{Re}Q_\alpha(\rho\Vert\sigma)=0,\\
--   D_\alpha(\rho\Vert\sigma),&\text{otherwise}.
--   \end{cases}
--   $$
--   The formal definition is total for real $\alpha$ and arbitrary operators; its intended entropy domain is $\rho,\sigma\ge0$, $\alpha>0$, $\alpha\ne1$. Values lie in $[-\infty,+\infty]$, with the finite branch in nats and no truncation to nonnegative reals or trace-one premise.
--
--   For positive semidefinite $\rho,\sigma$ satisfying the support condition, some $c>0$ satisfies $\rho\le c\sigma$; CPTP maps preserve this support inclusion. Completely positive maps preserve operator order, and positive operators with zero quadratic form annihilate the vector.
--
--   For finite-dimensional input $H$ and nonzero finite-dimensional output $K$, define the depolarizing CPTP map $\Delta_{H,K}(X)=\operatorname{Tr}(X)I_K/d_K$, where $d_K=\dim K$; the input may have dimension zero. Its Kraus formula uses scaled rank-one maps between orthonormal bases. For nonzero input and output, a CPTP map $\Phi$ and $0\le\lambda\le1$ give
--   $$
--   F_\lambda=(1-\lambda)\Phi+\lambda\Delta_{H,K}.
--   $$
--   The underlying linear map is defined for every real $\lambda$; the stated interval gives complete positivity and the bundled trace-preserving channel. Strictly positive output claims are established in later parts, not assumed in this definition.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/SandwichedRenyiNonNeg.lean#L52-L677

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

/-- **Support condition**: `ker σ ≤ ker ρ`, equivalent to `supp ρ ⊂ supp σ`. -/
def suppLE {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (ρ σ : L ℋ) : Prop :=
  LinearMap.ker σ ≤ LinearMap.ker ρ



/-! ### Frank–Lieb explicit formula -/

/-- **Frank–Lieb extended sandwiched Rényi divergence** for non-negative `ρ, σ`.

    For `α > 0`, `α ≠ 1`, the value is `⊤ : EReal` exactly on the region where the
    true divergence is `+∞`, and the real-valued `sandwichedRenyiDiv α ρ σ`
    (coerced to `EReal`) otherwise:

    * `α > 1` and `supp(ρ) ⊄ supp(σ)` (i.e. `¬ suppLE ρ σ`): value `⊤`.
      (`CFC.rpow σ ((1−α)/(2α))` would need the genuine inverse, divergent on `ker σ`.)
    * `α < 1` and `ρ ≠ 0` and `Q_α(ρ‖σ) = 0` (i.e. `ρ ⊥ σ`, orthogonal supports):
      value `⊤`. Here `Real.log 0 = 0` would otherwise give the *wrong* value `0`,
      whereas the true divergence is `+∞` (since `1/(α−1) < 0`).
    * otherwise: value `sandwichedRenyiDiv α ρ σ`.

    For `ρ, σ ∈ pdSetLM` the kernel of `σ` is trivial and `Q_α > 0`, so the formula
    agrees with the standard `sandwichedRenyiDiv α ρ σ` viewed in `EReal`. -/
noncomputable def sandwichedRenyiDivNN
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ] (α : ℝ) (ρ σ : L ℋ) : EReal :=
  letI : Decidable ((1 < α ∧ ¬ suppLE ρ σ) ∨
      (α < 1 ∧ ρ ≠ 0 ∧ (sandwichedQuasi α ρ σ).re = 0)) := Classical.propDecidable _
  if (1 < α ∧ ¬ suppLE ρ σ) ∨ (α < 1 ∧ ρ ≠ 0 ∧ (sandwichedQuasi α ρ σ).re = 0)
    then (⊤ : EReal)
  else ((sandwichedRenyiDiv α ρ σ : ℝ) : EReal)

/-! ### Auxiliary spectral / order lemmas -/

/-- The completely positive map underlying a `CPTP` preserves `≤` on its domain. -/
lemma map_le_map_of_nonneg
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (F : CompletelyPositiveMap (L ℋ) (L 𝒦))
    {a b : L ℋ} (hab : a ≤ b) :
    F.toLinearMap a ≤ F.toLinearMap b := by
  have h : 0 ≤ b - a := sub_nonneg.mpr hab
  have hF : 0 ≤ F.toLinearMap (b - a) := map_nonneg F h
  rw [LinearMap.map_sub] at hF
  exact sub_nonneg.mp hF

/-- For non-negative `ρ, σ` in finite dimension with `ker σ ≤ ker ρ`, there
    exists `lam > 0` with `ρ ≤ lam • σ`.

    **Proof**: Case split on `σ = 0` (then `ρ = 0` by `suppLE`) vs `σ ≠ 0`.
    For `σ ≠ 0`, use the spectral decomposition of `σ`: let `b` be an orthonormal
    eigenbasis with eigenvalues `eig i ≥ 0`. Let `S = {i | eig i > 0}` (nonempty
    since `σ ≠ 0`) and `s_min = min over S of eig`. By `suppLE`, `ρ` annihilates
    eigenvectors with zero eigenvalue. Then for any `x`, expanding in the eigenbasis,
    `re ⟨x, ρ x⟩ ≤ ‖ρ‖ · ∑_{i ∈ S} |⟨b i, x⟩|² ≤ (‖ρ‖ / s_min) · re ⟨x, σ x⟩`.
    Hence `ρ ≤ (‖ρ‖ / s_min + 1) • σ`.

    **Status**: Fully proven. -/
lemma nonneg_le_smul_of_suppLE
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (h : suppLE ρ σ) :
    ∃ lam > (0 : ℝ), ρ ≤ (lam : ℂ) • σ := by
  by_cases hσ_zero : σ = 0
  · -- `σ = 0`: then `ker σ = ⊤`, by `suppLE` also `ker ρ = ⊤`, so `ρ = 0`. Take `lam = 1`.
    have hker_σ : LinearMap.ker σ = ⊤ := by
      rw [hσ_zero, LinearMap.ker_zero]
    have hker_ρ : LinearMap.ker ρ = ⊤ := eq_top_iff.mpr (hker_σ ▸ h)
    have hρ_zero : ρ = 0 := by
      ext x
      have : x ∈ LinearMap.ker ρ := by rw [hker_ρ]; trivial
      exact this
    exact ⟨1, one_pos, by rw [hρ_zero, hσ_zero]; simp⟩
  · -- `σ ≠ 0`: spectral argument.
    classical
    have hρ_pos : ρ.IsPositive := (LinearMap.nonneg_iff_isPositive ρ).mp hρ
    have hσ_pos : σ.IsPositive := (LinearMap.nonneg_iff_isPositive σ).mp hσ
    have hσ_sym : σ.IsSymmetric := hσ_pos.isSymmetric
    have hρ_sym : ρ.IsSymmetric := hρ_pos.isSymmetric
    set n := Module.finrank ℂ ℋ with hn_def
    have hn : Module.finrank ℂ ℋ = n := rfl
    set b : OrthonormalBasis (Fin n) ℂ ℋ := hσ_sym.eigenvectorBasis hn with hb_def
    set eig : Fin n → ℝ := hσ_sym.eigenvalues hn with heig_def
    have h_eig_nn : ∀ i, (0:ℝ) ≤ eig i := fun i => hσ_pos.nonneg_eigenvalues hn i
    have h_eig_apply : ∀ i, σ (b i) = ((eig i : ℝ) : ℂ) • (b i : ℋ) :=
      hσ_sym.apply_eigenvectorBasis hn
    -- Show ∃ i, 0 < eig i (using σ ≠ 0).
    have h_exists_pos : ∃ i, 0 < eig i := by
      by_contra h_all
      push_neg at h_all
      have h_all_zero : ∀ i, eig i = 0 := fun i => le_antisymm (h_all i) (h_eig_nn i)
      apply hσ_zero
      ext v
      have hv : v = ∑ i, b.repr v i • (b i : ℋ) := (b.sum_repr v).symm
      conv_lhs => rw [hv]
      rw [map_sum]
      refine Finset.sum_eq_zero ?_
      intro i _
      rw [LinearMap.map_smul, h_eig_apply i, h_all_zero i]
      simp
    -- Define `S := {i | 0 < eig i}` and `s_min := min over S`.
    set S : Finset (Fin n) := Finset.univ.filter (fun i => 0 < eig i) with hS_def
    have hS_nonempty : S.Nonempty := by
      obtain ⟨i, hi⟩ := h_exists_pos
      exact ⟨i, by simp [S, hi]⟩
    set s_min : ℝ := S.inf' hS_nonempty eig with hs_min_def
    have hs_min_pos : 0 < s_min := by
      apply (Finset.lt_inf'_iff hS_nonempty).mpr
      intro j hj
      exact (Finset.mem_filter.mp hj).2
    have hs_min_le : ∀ i ∈ S, s_min ≤ eig i := fun i hi => Finset.inf'_le _ hi
    -- Characterize membership in S: `i ∈ S ↔ 0 < eig i ↔ eig i ≠ 0`.
    have h_mem_S : ∀ i, i ∈ S ↔ eig i ≠ 0 := by
      intro i
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi; exact ne_of_gt hi
      · intro hi
        rcases eq_or_lt_of_le (h_eig_nn i) with h_eq | h_lt
        · exact absurd h_eq.symm hi
        · exact h_lt
    -- For `i ∉ S`, `ρ (b i) = 0` (from `suppLE`).
    have h_ρ_ker : ∀ i, i ∉ S → ρ (b i) = 0 := by
      intro i hi
      have h_eig_i_zero : eig i = 0 := by
        by_contra h_ne
        exact hi ((h_mem_S i).mpr h_ne)
      have h_σ_bi : σ (b i) = 0 := by
        rw [h_eig_apply i, h_eig_i_zero]; simp
      have h_bi_ker : b i ∈ LinearMap.ker σ := h_σ_bi
      exact h h_bi_ker
    -- Set `lam := ‖ρ‖ / s_min + 1`.
    refine ⟨‖ρ‖ / s_min + 1, by positivity, ?_⟩
    -- Show `ρ ≤ lam • σ` via `IsPositive (lam • σ - ρ)`.
    rw [LinearMap.le_def]
    refine ⟨?_, ?_⟩
    · -- Symmetry of `lam • σ - ρ`.
      have hsmul_sym : (((‖ρ‖ / s_min + 1 : ℝ) : ℂ) • σ).IsSymmetric := by
        intro u w
        change inner ℂ (((‖ρ‖ / s_min + 1 : ℝ) : ℂ) • σ u) w =
          inner ℂ u (((‖ρ‖ / s_min + 1 : ℝ) : ℂ) • σ w)
        rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal, hσ_sym u w]
      exact hsmul_sym.sub hρ_sym
    · -- `0 ≤ re ⟨(lam • σ - ρ) x, x⟩` for all x.
      intro x
      -- Step 1: `⟨b i, σ x⟩ = eig i * ⟨b i, x⟩`.
      have h_σ_inner : ∀ i, inner ℂ (b i : ℋ) (σ x) =
          ((eig i : ℝ) : ℂ) * inner ℂ (b i : ℋ) x := by
        intro i
        have h1 : inner ℂ (b i : ℋ) (σ x) = inner ℂ (σ (b i)) x := (hσ_sym (b i) x).symm
        rw [h1, h_eig_apply i, inner_smul_left, Complex.conj_ofReal]
      -- Step 2: `re ⟨x, σ x⟩ = ∑ i, eig i * ‖⟨b i, x⟩‖²`.
      have h_re_σ : RCLike.re (inner ℂ x (σ x)) =
          ∑ i, eig i * ‖inner ℂ (b i : ℋ) x‖^2 := by
        rw [← b.sum_inner_mul_inner x (σ x), map_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [h_σ_inner i]
        rw [show inner ℂ x (b i : ℋ) =
              (starRingEnd ℂ) (inner ℂ (b i : ℋ) x) from (inner_conj_symm x (b i : ℋ)).symm]
        rw [show (starRingEnd ℂ) (inner ℂ (b i : ℋ) x) *
              (((eig i : ℝ) : ℂ) * inner ℂ (b i : ℋ) x) =
              ((eig i : ℝ) : ℂ) *
                ((starRingEnd ℂ) (inner ℂ (b i : ℋ) x) * inner ℂ (b i : ℋ) x) by ring]
        rw [show (starRingEnd ℂ) (inner ℂ (b i : ℋ) x) * inner ℂ (b i : ℋ) x =
              ((‖inner ℂ (b i : ℋ) x‖^2 : ℝ) : ℂ) by
                rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]]
        rw [show ((eig i : ℝ) : ℂ) * ((‖inner ℂ (b i : ℋ) x‖^2 : ℝ) : ℂ) =
              ((eig i * ‖inner ℂ (b i : ℋ) x‖^2 : ℝ) : ℂ) by push_cast; ring]
        exact Complex.ofReal_re _
      -- Step 3: each term in re ⟨x, σ x⟩ is nonneg, so re ⟨x, σ x⟩ ≥ 0 and
      -- the sum restricted to S is bounded: s_min * (∑ S terms) ≤ re ⟨x, σ x⟩.
      have h_sum_S_le : s_min * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2) ≤
          RCLike.re (inner ℂ x (σ x)) := by
        rw [h_re_σ, Finset.mul_sum]
        -- ∑ i ∈ S, s_min * ‖⟨b i, x⟩‖² ≤ ∑ i, eig i * ‖⟨b i, x⟩‖²
        have h_le_full : (∑ i ∈ S, s_min * ‖inner ℂ (b i : ℋ) x‖^2) ≤
            ∑ i ∈ S, eig i * ‖inner ℂ (b i : ℋ) x‖^2 := by
          apply Finset.sum_le_sum
          intro i hi
          apply mul_le_mul_of_nonneg_right (hs_min_le i hi) (sq_nonneg _)
        refine h_le_full.trans ?_
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
        intros j _ hj
        rw [show eig j = 0 from by
          by_contra h_ne; exact hj ((h_mem_S j).mpr h_ne)]
        simp
      -- Step 4: bound `re ⟨ρ x, x⟩ ≤ ‖ρ‖ * ∑ i ∈ S, ‖⟨b i, x⟩‖²`.
      -- Define xS := ∑ i ∈ S, ⟨b i, x⟩ • b i.
      set xS : ℋ := ∑ i ∈ S, inner ℂ (b i : ℋ) x • (b i : ℋ) with hxS_def
      have hx_decomp : x = ∑ i, inner ℂ (b i : ℋ) x • (b i : ℋ) := by
        conv_lhs => rw [← b.sum_repr x]
        apply Finset.sum_congr rfl
        intro i _
        rw [b.repr_apply_apply]
      -- `ρ x = ρ xS` (using `h_ρ_ker`).
      have h_ρ_x_eq : ρ x = ρ xS := by
        rw [hx_decomp, map_sum, hxS_def, map_sum]
        refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
        intros i _ hi
        rw [LinearMap.map_smul, h_ρ_ker i hi, smul_zero]
      -- `inner ℂ (ρ x) x = inner ℂ (ρ xS) xS`:
      -- use orthogonality `⟨ρ xS, b i⟩ = ⟨xS, ρ b i⟩ = 0` for `i ∉ S`.
      have h_inner_ρ_eq : inner ℂ (ρ x) x = inner ℂ (ρ xS) xS := by
        rw [h_ρ_x_eq]
        -- Use sum_inner_mul_inner to expand both sides in the basis.
        rw [← b.sum_inner_mul_inner (ρ xS) x, ← b.sum_inner_mul_inner (ρ xS) xS]
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i ∈ S
        · -- For `i ∈ S`: `⟨b i, x⟩ = ⟨b i, xS⟩` by orthonormality.
          have h_bi_xS : inner ℂ (b i : ℋ) xS = inner ℂ (b i : ℋ) x := by
            rw [hxS_def, inner_sum]
            rw [show ∑ j ∈ S, inner ℂ (b i : ℋ) (inner ℂ (b j : ℋ) x • (b j : ℋ)) =
                inner ℂ (b i : ℋ) x from by
              rw [Finset.sum_eq_single i (fun j _ hji => ?_) (fun hi' => absurd hi hi')]
              · rw [inner_smul_right, b.inner_eq_one i]; ring
              · rw [inner_smul_right]
                rw [show inner ℂ (b i : ℋ) (b j : ℋ) = 0 from
                    b.orthonormal.2 (by exact fun h => hji h.symm)]
                ring]
          rw [h_bi_xS]
        · -- For `i ∉ S`: `⟨ρ xS, b i⟩ = ⟨xS, ρ (b i)⟩ = 0`.
          have h_inner_zero : inner ℂ (ρ xS) (b i : ℋ) = 0 := by
            rw [show inner ℂ (ρ xS) (b i : ℋ) = inner ℂ xS (ρ (b i)) from hρ_sym xS (b i)]
            rw [h_ρ_ker i hi]
            simp
          rw [h_inner_zero, zero_mul, zero_mul]
      -- Operator-norm bound: `re ⟨ρ xS, xS⟩ ≤ ‖ρ‖ * ‖xS‖²`.
      have h_op_bound : RCLike.re (inner ℂ (ρ xS) xS) ≤ ‖ρ‖ * ‖xS‖^2 := by
        have h1 : RCLike.re (inner ℂ (ρ xS) xS) ≤ ‖inner ℂ (ρ xS) xS‖ := RCLike.re_le_norm _
        have h2 : ‖inner ℂ (ρ xS) xS‖ ≤ ‖ρ xS‖ * ‖xS‖ := norm_inner_le_norm _ _
        have h3 : ‖ρ xS‖ ≤ ‖ρ‖ * ‖xS‖ := by
          have := ρ.toContinuousLinearMap.le_opNorm xS
          simpa using this
        calc RCLike.re (inner ℂ (ρ xS) xS) ≤ ‖inner ℂ (ρ xS) xS‖ := h1
          _ ≤ ‖ρ xS‖ * ‖xS‖ := h2
          _ ≤ (‖ρ‖ * ‖xS‖) * ‖xS‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
          _ = ‖ρ‖ * ‖xS‖^2 := by ring
      -- ‖xS‖² = ∑ i ∈ S, ‖⟨b i, x⟩‖² (orthonormality + ‖∑ a_i e_i‖² = ∑ ‖a_i‖²).
      have h_xS_norm_sq : ‖xS‖^2 = ∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2 := by
        rw [hxS_def, @norm_sq_eq_re_inner ℂ]
        rw [inner_sum]
        simp_rw [sum_inner, inner_smul_left, inner_smul_right]
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [show (∑ j ∈ S, (starRingEnd ℂ) (inner ℂ (b j : ℋ) x) *
                ((inner ℂ (b i : ℋ) x) * inner ℂ (b j : ℋ) (b i : ℋ))) =
                ((‖inner ℂ (b i : ℋ) x‖^2 : ℝ) : ℂ) from ?_]
        · exact Complex.ofReal_re _
        · rw [Finset.sum_eq_single i ?_ ?_]
          · rw [b.inner_eq_one i, mul_one, mul_comm, Complex.mul_conj,
                Complex.normSq_eq_norm_sq]
          · intros j _ hji
            rw [show inner ℂ (b j : ℋ) (b i : ℋ) = 0 from
                  b.orthonormal.2 hji]
            ring
          · intro hiS
            exact absurd hi hiS
      -- Step 5: combine into final inequality `re ⟨(lam • σ - ρ) x, x⟩ ≥ 0`.
      have h_sum_nn : (0 : ℝ) ≤ ∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2 :=
        Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      have h_ρ_bound : RCLike.re (inner ℂ (ρ x) x) ≤
          ‖ρ‖ * ∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2 := by
        rw [h_inner_ρ_eq, ← h_xS_norm_sq]
        exact h_op_bound
      have h_σ_bound : s_min * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2) ≤
          RCLike.re (inner ℂ (σ x) x) := by
        rw [show inner ℂ (σ x) x = inner ℂ x (σ x) from hσ_sym x x]
        exact h_sum_S_le
      have h_σ_nn : (0 : ℝ) ≤ RCLike.re (inner ℂ (σ x) x) := hσ_pos.2 x
      have h_ρ_norm_nn : (0 : ℝ) ≤ ‖ρ‖ := norm_nonneg _
      have h_unfold_sub : (((‖ρ‖ / s_min + 1 : ℝ) : ℂ) • σ - ρ) x =
          ((‖ρ‖ / s_min + 1 : ℝ) : ℂ) • σ x - ρ x := by
        rw [LinearMap.sub_apply, LinearMap.smul_apply]
      rw [h_unfold_sub, inner_sub_left, inner_smul_left, Complex.conj_ofReal, map_sub]
      have h_re_eq : RCLike.re (((‖ρ‖ / s_min + 1 : ℝ) : ℂ) * inner ℂ (σ x) x) =
          (‖ρ‖ / s_min + 1) * RCLike.re (inner ℂ (σ x) x) := by
        change ((((‖ρ‖ / s_min + 1 : ℝ) : ℂ) * inner ℂ (σ x) x)).re = _
        rw [Complex.re_ofReal_mul]
        rfl
      rw [h_re_eq]
      -- Goal: 0 ≤ (‖ρ‖/s_min + 1) * re ⟨σ x, x⟩ - re ⟨ρ x, x⟩
      have h_combine : RCLike.re (inner ℂ (ρ x) x) ≤
          (‖ρ‖ / s_min + 1) * RCLike.re (inner ℂ (σ x) x) := by
        have h1 : ‖ρ‖ * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2) =
            (‖ρ‖ / s_min) * (s_min * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2)) := by
          field_simp
        have h2 : (‖ρ‖ / s_min) * (s_min * (∑ i ∈ S, ‖inner ℂ (b i : ℋ) x‖^2)) ≤
            (‖ρ‖ / s_min) * RCLike.re (inner ℂ (σ x) x) :=
          mul_le_mul_of_nonneg_left h_σ_bound (div_nonneg h_ρ_norm_nn hs_min_pos.le)
        have h3 : (‖ρ‖ / s_min) * RCLike.re (inner ℂ (σ x) x) ≤
            (‖ρ‖ / s_min + 1) * RCLike.re (inner ℂ (σ x) x) := by
          have h_le : ‖ρ‖ / s_min ≤ ‖ρ‖ / s_min + 1 := by linarith
          exact mul_le_mul_of_nonneg_right h_le h_σ_nn
        linarith
      linarith

/-- For a non-negative operator `A`, `re ⟨A x, x⟩ = 0` implies `A x = 0`.

    **Proof**: For positive `A`, take `s := CFC.sqrt A`. Then `s` is symmetric,
    `s * s = A`, and `re ⟨A x, x⟩ = re ⟨s (s x), x⟩ = re ⟨s x, s x⟩ = ‖s x‖² = 0`.
    Hence `s x = 0` and `A x = s (s x) = 0`. -/
lemma nonneg_apply_eq_zero_of_inner_self_eq_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A : L ℋ} (hA : 0 ≤ A) {x : ℋ}
    (h_inner : RCLike.re (inner ℂ (A x) x) = 0) :
    A x = 0 := by
  set s : L ℋ := CFC.sqrt A with hs_def
  have hs_nn : (0 : L ℋ) ≤ s := CFC.sqrt_nonneg A
  have hs_sq : s * s = A := CFC.sqrt_mul_sqrt_self A
  have hs_pos : s.IsPositive := (LinearMap.nonneg_iff_isPositive s).mp hs_nn
  have hs_sym : s.IsSymmetric := hs_pos.1
  have h_s_apply : s (s x) = A x := by
    have : (s * s) x = A x := by rw [hs_sq]
    exact this
  have h_norm_sq : ‖s x‖ ^ 2 = RCLike.re (inner ℂ (A x) x) := by
    have h1 : inner ℂ (s x) (s x) = inner ℂ (s (s x)) x := (hs_sym (s x) x).symm
    have h2 : inner ℂ (s (s x)) x = inner ℂ (A x) x := by rw [h_s_apply]
    have h3 : (inner ℂ (s x) (s x) : ℂ) = inner ℂ (A x) x := h1.trans h2
    rw [← @inner_self_eq_norm_sq ℂ ℋ, h3]
  rw [h_inner] at h_norm_sq
  have h_sx_norm : ‖s x‖ = 0 := by
    have h_pow : ‖s x‖ ^ 2 = 0 := h_norm_sq
    exact pow_eq_zero_iff two_ne_zero |>.mp h_pow
  have h_sx : s x = 0 := norm_eq_zero.mp h_sx_norm
  rw [← h_s_apply, h_sx, LinearMap.map_zero]

/-- For non-negative `A ≤ B`, `B x = 0 ⇒ A x = 0`.

    **Proof**: From `A ≤ B`, `0 ≤ A`, and `B x = 0`, derive `re ⟨A x, x⟩ = 0`, then
    apply `nonneg_apply_eq_zero_of_inner_self_eq_zero`. -/
lemma nonneg_eq_zero_of_le_of_apply_eq_zero
    {ℋ : Type u} [Qudit ℋ] [Nontrivial ℋ]
    {A B : L ℋ} (hA : 0 ≤ A) (hAB : A ≤ B) {x : ℋ} (hx : B x = 0) :
    A x = 0 := by
  -- Step 1: `re ⟪A x, x⟫ = 0`.
  have hBA : 0 ≤ B - A := sub_nonneg.mpr hAB
  have hA_pos : A.IsPositive := (LinearMap.nonneg_iff_isPositive A).mp hA
  have hBA_pos : (B - A).IsPositive := (LinearMap.nonneg_iff_isPositive _).mp hBA
  have h_A_nn : (0 : ℝ) ≤ RCLike.re (inner ℂ (A x) x) := hA_pos.2 x
  have h_BA_nn : (0 : ℝ) ≤ RCLike.re (inner ℂ ((B - A) x) x) := hBA_pos.2 x
  have hsub_x : (B - A) x = -A x := by
    change B x - A x = -A x
    rw [hx, zero_sub]
  have h_BA_eq : RCLike.re (inner ℂ ((B - A) x) x) = -RCLike.re (inner ℂ (A x) x) := by
    rw [hsub_x, inner_neg_left, map_neg]
  rw [h_BA_eq] at h_BA_nn
  have h_A_zero : RCLike.re (inner ℂ (A x) x) = 0 := le_antisymm (by linarith) h_A_nn
  -- Step 2: apply the core lemma.
  exact nonneg_apply_eq_zero_of_inner_self_eq_zero hA h_A_zero

/-! ### Support preservation under positive maps -/

/-- Positive maps preserve the support inclusion: if `supp ρ ⊂ supp σ` and `E` is
    a positive linear map (in particular, CPTP), then `supp (E ρ) ⊂ supp (E σ)`. -/
lemma suppLE_of_CPTP
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {ρ σ : L ℋ} (hρ : 0 ≤ ρ) (hσ : 0 ≤ σ) (h : suppLE ρ σ) :
    suppLE (E.toFun ρ) (E.toFun σ) := by
  intro x hx
  have hEρ_nn : 0 ≤ E.toFun ρ := map_nonneg E.toCompletelyPositiveMap hρ
  have hEσ_nn : 0 ≤ E.toFun σ := map_nonneg E.toCompletelyPositiveMap hσ
  obtain ⟨lam, hlam_pos, hlam_le⟩ := nonneg_le_smul_of_suppLE hρ hσ h
  have hEρ_le : E.toFun ρ ≤ (lam : ℂ) • E.toFun σ := by
    have h1 : E.toCompletelyPositiveMap.toLinearMap ρ ≤
        E.toCompletelyPositiveMap.toLinearMap ((lam : ℂ) • σ) :=
      map_le_map_of_nonneg E.toCompletelyPositiveMap hlam_le
    rw [LinearMap.map_smul] at h1
    exact h1
  exact nonneg_eq_zero_of_le_of_apply_eq_zero hEρ_nn hEρ_le (by
    rw [LinearMap.smul_apply, hx, smul_zero])

/-! ### Outer-product helpers and the depolarizing-channel Kraus decomposition -/

/-- Application of an outer product: `(|v⟩⟨u|) x = ⟪u, x⟫ • v`. -/
 lemma outer_product_apply {ℋ₁ ℋ₂ : Type u} [Qudit ℋ₁] [Qudit ℋ₂]
    (u : ℋ₁) (v : ℋ₂) (x : ℋ₁) :
    outer_product u v x = (inner ℂ u x : ℂ) • v := by
  rw [outer_product_eq_rankOne]
  simp [InnerProductSpace.rankOne_apply]



/-- **Kraus sum for the (cross-space) depolarizing channel.** With `bp` an orthonormal basis
    of the target `𝒦`, `bq` an orthonormal basis of the source `ℋ`, and a real scalar `c`,
    `∑_{i,j} (c • |bp i⟩⟨bq j|) γ (c • |bp i⟩⟨bq j|)† = (c² · Tr γ) • 1_𝒦`. -/
 lemma depolarizing_kraus_sum
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Qudit 𝒦]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (bp : OrthonormalBasis ι ℂ 𝒦) (bq : OrthonormalBasis κ ℂ ℋ)
    (γ : L ℋ) (c : ℝ) :
    (∑ p : ι × κ, (krausTerm ((c : ℂ) • outer_product (bq p.2) (bp p.1)) : T ℋ 𝒦) γ)
      = ((c : ℂ) ^ 2 * Tr γ) • (1 : L 𝒦) := by
  classical
  -- Per-term: `(c•|eᵢ⟩⟨fⱼ|) γ (c•|eᵢ⟩⟨fⱼ|)† = c² ⟪fⱼ, γ fⱼ⟫ • |eᵢ⟩⟨eᵢ|`.
  have hterm : ∀ (i : ι) (j : κ),
      (krausTerm ((c : ℂ) • outer_product (bq j) (bp i)) : T ℋ 𝒦) γ
        = ((c : ℂ) ^ 2 * inner ℂ (bq j) (γ (bq j))) • outer_product (bp i) (bp i) := by
    intro i j
    have hadj : LinearMap.adjoint ((c : ℂ) • outer_product (bq j) (bp i))
        = (c : ℂ) • outer_product (bp i) (bq j) := by
      apply LinearMap.ext; intro x
      apply ext_inner_right ℂ; intro y
      rw [LinearMap.adjoint_inner_left]
      simp only [LinearMap.smul_apply, _root_.SandwichedRenyiRelativeEntropy.outer_product_apply, inner_smul_right,
        inner_smul_left, inner_conj_symm, Complex.conj_ofReal]
      ring
    apply LinearMap.ext; intro x
    have hkt : (krausTerm ((c : ℂ) • outer_product (bq j) (bp i)) : T ℋ 𝒦) γ
        = ((c : ℂ) • outer_product (bq j) (bp i)) ∘ₗ γ ∘ₗ
            ((c : ℂ) • outer_product (bp i) (bq j)) := by
      change ((c : ℂ) • outer_product (bq j) (bp i)) ∘ₗ γ ∘ₗ
          LinearMap.adjoint ((c : ℂ) • outer_product (bq j) (bp i)) = _
      rw [hadj]
    rw [hkt]
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul, _root_.SandwichedRenyiRelativeEntropy.outer_product_apply,
      smul_smul]
    congr 1
    ring
  -- Reassemble the double sum into `(c² · Tr γ) • 1_𝒦`.
  have hTr : (∑ j, inner ℂ (bq j) (γ (bq j))) = Tr γ :=
    (LinearMap.trace_eq_sum_inner (T := γ) bq).symm
  have hId : (∑ i, outer_product (bp i) (bp i)) = (1 : L 𝒦) := by
    have h := linearMap_eq_sum_outer_product bp (1 : L 𝒦)
    simp only [Module.End.one_apply] at h
    exact h.symm
  simp_rw [hterm]
  rw [Fintype.sum_prod_type]
  have step1 : ∀ i : ι,
      (∑ j, ((c : ℂ) ^ 2 * inner ℂ (bq j) (γ (bq j))) • outer_product (bp i) (bp i))
        = ((c : ℂ) ^ 2 * Tr γ) • outer_product (bp i) (bp i) := by
    intro i
    rw [← Finset.sum_smul, ← Finset.mul_sum, hTr]
  simp_rw [step1]
  rw [← Finset.smul_sum, hId]

/-- The (cross-space) depolarizing channel's underlying linear map `γ ↦ (Tr γ / d_𝒦) • 1_𝒦`. -/
noncomputable def depolLinMap (ℋ 𝒦 : Type u) [Qudit ℋ] [Qudit 𝒦] [Nontrivial 𝒦] :
    L ℋ →ₗ[ℂ] L 𝒦 where
  toFun γ := (Tr γ / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)
  map_add' x y := by
    change (Tr (x + y) / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) =
         (Tr x / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) +
         (Tr y / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)
    rw [map_add, add_div, add_smul]
  map_smul' c x := by
    change (Tr (c • x) / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) =
         (RingHom.id ℂ) c • ((Tr x / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦))
    rw [map_smul, smul_eq_mul, RingHom.id_apply, mul_div_assoc, mul_smul]

/-- **Complete positivity of the (cross-space) depolarizing channel**, via the Kraus
    decomposition `depolLinMap = ∑_{i,j} krausTerm ((√d_𝒦)⁻¹ • |i⟩⟨j|)`. -/
lemma depolLinMap_isCompletelyPositive (ℋ 𝒦 : Type u) [Qudit ℋ] [Qudit 𝒦] [Nontrivial 𝒦] :
    IsCompletelyPositive (depolLinMap ℋ 𝒦) := by
  classical
  set m := Module.finrank ℂ 𝒦 with hm
  set n := Module.finrank ℂ ℋ with hn
  set bp : OrthonormalBasis (Fin m) ℂ 𝒦 := stdOrthonormalBasis ℂ 𝒦 with hbp
  set bq : OrthonormalBasis (Fin n) ℂ ℋ := stdOrthonormalBasis ℂ ℋ with hbq
  set V : Fin m × Fin n → (ℋ →ₗ[ℂ] 𝒦) :=
    fun p => (((Real.sqrt (m : ℝ))⁻¹ : ℝ) : ℂ) • outer_product (bq p.2) (bp p.1) with hV
  have hm_nn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hc2 : ((((Real.sqrt (m : ℝ))⁻¹ : ℝ)) : ℂ) ^ 2 = ((m : ℂ))⁻¹ := by
    rw [← Complex.ofReal_pow, inv_pow, Real.sq_sqrt hm_nn, Complex.ofReal_inv,
        Complex.ofReal_natCast]
  have hmap : depolLinMap ℋ 𝒦 = ∑ p : Fin m × Fin n, krausTerm (V p) := by
    apply LinearMap.ext; intro γ
    rw [LinearMap.sum_apply]
    change (Tr γ / (m : ℂ)) • (1 : L 𝒦) =
        ∑ p : Fin m × Fin n, (krausTerm (V p) : T ℋ 𝒦) γ
    rw [_root_.SandwichedRenyiRelativeEntropy.depolarizing_kraus_sum bp bq γ ((Real.sqrt (m : ℝ))⁻¹), hc2]
    congr 1
    ring
  rw [hmap]
  exact sum_krausTerm_isCompletelyPositive V

/-! ### Faithful approximating channel `F_λ := (1−λ) E + λ · depolarizing` -/

/-- The (cross-space) depolarizing channel `γ ↦ (Tr γ / d_𝒦) • 1_𝒦`, as a CPTP map `ℋ → 𝒦`.

    Complete positivity comes from the Kraus decomposition
    (`depolLinMap_isCompletelyPositive`); trace preservation is
    `Tr((Tr γ / d_𝒦) • 1_𝒦) = (Tr γ / d_𝒦) · d_𝒦 = Tr γ`. -/
noncomputable def depolarizingChannel
    (ℋ 𝒦 : Type u) [Qudit ℋ] [Qudit 𝒦] [Nontrivial 𝒦] : CPTP ℋ 𝒦 where
  toFun γ := (Tr γ / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)
  map_add' x y := by
    change (Tr (x + y) / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) =
         (Tr x / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) +
         (Tr y / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦)
    rw [map_add, add_div, add_smul]
  map_smul' c x := by
    change (Tr (c • x) / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦) =
         (RingHom.id ℂ) c • ((Tr x / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦))
    rw [map_smul, smul_eq_mul, RingHom.id_apply, mul_div_assoc, mul_smul]
  map_cstarMatrix_nonneg' k M hM := by
    -- Complete positivity via the Kraus decomposition of the underlying linear map.
    obtain ⟨Ψ, hΨ⟩ := depolLinMap_isCompletelyPositive ℋ 𝒦
    have h := Ψ.map_cstarMatrix_nonneg' k M hM
    rw [hΨ] at h
    exact h
  trace_map ρ := by
    show Tr ρ = Tr ((Tr ρ / (Module.finrank ℂ 𝒦 : ℂ)) • (1 : L 𝒦))
    rw [map_smul, smul_eq_mul, LinearMap.trace_one,
        div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr Module.finrank_pos.ne')]

/-- The underlying linear map of the faithful approximation
    `F_λ := (1 − λ) E + λ · depolarizing`. -/
noncomputable def faithfulApproxLin
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) (lam : ℝ) : L ℋ →ₗ[ℂ] L 𝒦 where
  toFun γ := ((1 - lam : ℝ) : ℂ) • E.toFun γ +
             ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun γ
  map_add' x y := by
    have hE : E.toFun (x + y) = E.toFun x + E.toFun y :=
      LinearMap.map_add E.toCompletelyPositiveMap.toLinearMap x y
    have hD : (depolarizingChannel ℋ 𝒦).toFun (x + y) =
              (depolarizingChannel ℋ 𝒦).toFun x + (depolarizingChannel ℋ 𝒦).toFun y :=
      LinearMap.map_add (depolarizingChannel ℋ 𝒦).toCompletelyPositiveMap.toLinearMap x y
    change ((1 - lam : ℝ) : ℂ) • E.toFun (x + y) +
         ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun (x + y) =
         (((1 - lam : ℝ) : ℂ) • E.toFun x +
           ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun x) +
         (((1 - lam : ℝ) : ℂ) • E.toFun y +
           ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun y)
    rw [hE, hD, smul_add, smul_add]
    abel
  map_smul' c x := by
    have hE : E.toFun (c • x) = c • E.toFun x :=
      LinearMap.map_smul E.toCompletelyPositiveMap.toLinearMap c x
    have hD : (depolarizingChannel ℋ 𝒦).toFun (c • x) = c • (depolarizingChannel ℋ 𝒦).toFun x :=
      LinearMap.map_smul (depolarizingChannel ℋ 𝒦).toCompletelyPositiveMap.toLinearMap c x
    change ((1 - lam : ℝ) : ℂ) • E.toFun (c • x) +
         ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun (c • x) =
         (RingHom.id ℂ) c •
           (((1 - lam : ℝ) : ℂ) • E.toFun x +
             ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun x)
    rw [hE, hD, RingHom.id_apply, smul_add]
    simp_rw [smul_smul]
    rw [mul_comm c (((1 - lam : ℝ) : ℂ)), mul_comm c (((lam : ℝ) : ℂ))]

/-- **Complete positivity of the convex combination** `F_λ = (1−λ) E + λ D`
    (`0 ≤ λ ≤ 1`): entrywise, `M.map F_λ = (1−λ) • M.map E + λ • M.map D`, a
    non-negative combination of the non-negative matrices `M.map E`, `M.map D`. -/
lemma faithfulApproxLin_isCompletelyPositive
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) {lam : ℝ} (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    IsCompletelyPositive (faithfulApproxLin E lam) := by
  refine (isCompletelyPositive_iff_cstarMatrix_nonneg _).mpr (fun k M hM => ?_)
  have hE : 0 ≤ M.map E.toLinearMap := E.map_cstarMatrix_nonneg' k M hM
  have hD : 0 ≤ M.map (depolarizingChannel ℋ 𝒦).toLinearMap :=
    (depolarizingChannel ℋ 𝒦).map_cstarMatrix_nonneg' k M hM
  have heq : M.map (faithfulApproxLin E lam)
      = ((1 - lam : ℝ) : ℂ) • M.map E.toLinearMap
        + ((lam : ℝ) : ℂ) • M.map (depolarizingChannel ℋ 𝒦).toLinearMap := by
    ext i j
    simp only [CStarMatrix.map_apply]
    rfl
  -- Non-negative real scalar multiples preserve positivity (via `c•X = star(√c•1)·X·(√c•1)`).
  have hsmul : ∀ (r : ℝ), 0 ≤ r → ∀ (X : CStarMatrix (Fin k) (Fin k) (L 𝒦)), 0 ≤ X →
      0 ≤ ((r : ℝ) : ℂ) • X := by
    intro r hr X hX
    exact smul_nonneg (Complex.zero_le_real.mpr hr) hX
  rw [heq]
  exact add_nonneg (hsmul (1 - lam) (by linarith) _ hE) (hsmul lam hlam0 _ hD)

/-- The faithful approximating channel `F_λ := (1 − λ) E + λ · depolarizing`. -/
noncomputable def faithfulApprox
    {ℋ 𝒦 : Type u} [Qudit ℋ] [Nontrivial ℋ] [Qudit 𝒦] [Nontrivial 𝒦]
    (E : CPTP ℋ 𝒦) (lam : ℝ) (_hlam0 : 0 ≤ lam) (_hlam1 : lam ≤ 1) : CPTP ℋ 𝒦 where
  toFun γ := ((1 - lam : ℝ) : ℂ) • E.toFun γ +
             ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun γ
  map_add' x y := by
    have hE : E.toFun (x + y) = E.toFun x + E.toFun y :=
      LinearMap.map_add E.toCompletelyPositiveMap.toLinearMap x y
    have hD : (depolarizingChannel ℋ 𝒦).toFun (x + y) =
              (depolarizingChannel ℋ 𝒦).toFun x + (depolarizingChannel ℋ 𝒦).toFun y :=
      LinearMap.map_add (depolarizingChannel ℋ 𝒦).toCompletelyPositiveMap.toLinearMap x y
    change ((1 - lam : ℝ) : ℂ) • E.toFun (x + y) +
         ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun (x + y) =
         (((1 - lam : ℝ) : ℂ) • E.toFun x +
           ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun x) +
         (((1 - lam : ℝ) : ℂ) • E.toFun y +
           ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun y)
    rw [hE, hD, smul_add, smul_add]
    abel
  map_smul' c x := by
    have hE : E.toFun (c • x) = c • E.toFun x :=
      LinearMap.map_smul E.toCompletelyPositiveMap.toLinearMap c x
    have hD : (depolarizingChannel ℋ 𝒦).toFun (c • x) = c • (depolarizingChannel ℋ 𝒦).toFun x :=
      LinearMap.map_smul (depolarizingChannel ℋ 𝒦).toCompletelyPositiveMap.toLinearMap c x
    change ((1 - lam : ℝ) : ℂ) • E.toFun (c • x) +
         ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun (c • x) =
         (RingHom.id ℂ) c •
           (((1 - lam : ℝ) : ℂ) • E.toFun x +
             ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun x)
    rw [hE, hD, RingHom.id_apply, smul_add]
    simp_rw [smul_smul]
    rw [mul_comm c (((1 - lam : ℝ) : ℂ)), mul_comm c (((lam : ℝ) : ℂ))]
  map_cstarMatrix_nonneg' k M hM := by
    -- Complete positivity of the convex combination (`faithfulApproxLin_isCompletelyPositive`).
    obtain ⟨Ψ, hΨ⟩ := faithfulApproxLin_isCompletelyPositive E _hlam0 _hlam1
    have h := Ψ.map_cstarMatrix_nonneg' k M hM
    rw [hΨ] at h
    exact h
  trace_map ρ := by
    show Tr ρ = Tr (((1 - lam : ℝ) : ℂ) • E.toFun ρ +
                    ((lam : ℝ) : ℂ) • (depolarizingChannel ℋ 𝒦).toFun ρ)
    rw [map_add, LinearMap.map_smul, LinearMap.map_smul, smul_eq_mul, smul_eq_mul,
        ← E.trace_map ρ, ← (depolarizingChannel ℋ 𝒦).trace_map ρ]
    push_cast
    ring
end SandwichedRenyiRelativeEntropy


