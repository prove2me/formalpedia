-- Prove2me | Definitions.Def_CRCD_Quantum_TraceInequality_OperatorGeometricMean
-- name    : CRCD_Quantum_TraceInequality_OperatorGeometricMean
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T00:14:04.655409+00:00
-- url     : https://prove2.me/theorems/c2af7e2c-37f5-4ba8-8a2e-c7fe77e27a5d
-- title:
--   Two-parameter operator power mean
-- statement:
--   Let $H$ be a complete nonzero complex Hilbert space, let $A,B$ be bounded endomorphisms, and let $\alpha,\beta\in\mathbb R$. The two-parameter operator power mean is defined as the generalized perspective of the scalar powers $f(x)=x^\alpha$ and $h(x)=x^\beta$:
--
--   $$M_{\alpha,\beta}(A,B)=\mathcal H_+(B)\left[\mathcal H_-(B)A\mathcal H_-(B)\right]^\alpha\mathcal H_+(B),\qquad \mathcal H_\pm(B)=\operatorname{CFC}\!\left(x\mapsto(x^\beta)^{\pm1/2},B\right).$$
--
--   On strictly positive $B$, these factors agree with $B^{\beta/2}$ and $B^{-\beta/2}$, so the usual positive-operator formula results. The definition is total for arbitrary real parameters and operators; interpreting it as a positive mean or proving convexity or concavity requires the corresponding positivity and parameter hypotheses. No finite-dimensional assumption is imposed. This perspective-based interface supplies the operator mean used to obtain Lieb–Ando trace functionals through Hilbert–Schmidt multiplication representations.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/TraceInequality/OperatorGeometricMean.lean#L20-L116

import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Unitary.Span
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Definitions.Def_CRCD_Quantum_TraceInequality_BlockDiagonal
import Definitions.Def_CRCD_Quantum_TraceInequality_GeneralizedPerspectiveFunction
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequality
import Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_2
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzTheorem

/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/



namespace OperatorGeometricMean

universe u

open LownerHeinzTheorem
open GeneralizedPerspectiveFunction

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

/-- The operator `(α, β)`-power mean, realized as a generalized perspective. -/
noncomputable def operatorPowerMean (α β : ℝ) (A B : L ℋ) : L ℋ :=
  GeneralizedPerspective (fun x : ℝ ↦ x ^ α) (fun x : ℝ ↦ x ^ β) A B

 lemma rpow_continuousOn_Ici (p : ℝ) (hp : 0 ≤ p) :
    ContinuousOn (fun x : ℝ ↦ x ^ p) (Set.Ici (0 : ℝ)) := by
  intro x hx
  exact (Real.continuousAt_rpow_const x p (Or.inr hp)).continuousWithinAt

omit [Nontrivial ℋ] in
 lemma operatorConcaveOn_Ioi_of_Ici {f : ℝ → ℝ}
    (h : OperatorConcaveOn (ℋ := ℋ) (Set.Ici (0 : ℝ)) f) :
    OperatorConcaveOn (ℋ := ℋ) (Set.Ioi (0 : ℝ)) f := by
  intro A B t hA hB ht0 ht1 hAs hBs
  exact h hA hB ht0 ht1 (Set.Subset.trans hAs Set.Ioi_subset_Ici_self)
      (Set.Subset.trans hBs Set.Ioi_subset_Ici_self)

omit [Nontrivial ℋ] in
 lemma pdSet_subset_psdSet : pdSet (ℋ := ℋ) ⊆ psdSet (ℋ := ℋ) := by
  intro A hA
  rcases hA with ⟨hA_sa, hA_spec⟩
  exact ⟨hA_sa, Set.Subset.trans hA_spec Set.Ioi_subset_Ici_self⟩

 lemma rpow_pos_on_Ioi (p : ℝ) :
    ∀ x ∈ Set.Ioi (0 : ℝ), 0 < x ^ p := by
  intro x hx
  exact Real.rpow_pos_of_pos hx p

/--
Theorem 1.1, concave range: the operator `(α, β)`-power mean is jointly concave on
strictly positive operators for `0 ≤ α, β ≤ 1`.
-/
theorem operatorPowerMean_jointlyConcaveOn_pdSet
    {α β : ℝ}
    (hα : α ∈ Set.Icc (0 : ℝ) 1)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    JointlyConcaveOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (operatorPowerMean (ℋ := ℋ) α β) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hconc :=
    theorem_2_6_forward_jointlyConcaveOn_psd_pd_Ici
      (ℋ := ℋ)
      (f := fun x : ℝ ↦ x ^ α)
      (h := fun x : ℝ ↦ x ^ β)
      (hfconc := by
        intro K _ _ _ _
        exact power_Icc_zero_one_operatorConcaveOn_Ici (ℋ := K) α hα)
      (hfcont := _root_.OperatorGeometricMean.rpow_continuousOn_Ici α hα.1)
      (hf0 := by
        exact Real.rpow_nonneg (show (0 : ℝ) ≤ 0 by simp) α)
      (hconc := by
        exact _root_.OperatorGeometricMean.operatorConcaveOn_Ioi_of_Ici (ℋ := ℋ)
          (power_Icc_zero_one_operatorConcaveOn_Ici (ℋ := ℋ) β hβ))
      (hcont := by
        intro x hx
        exact (Real.continuousAt_rpow_const x β (Or.inl (ne_of_gt hx))).continuousWithinAt)
      (hpos := _root_.OperatorGeometricMean.rpow_pos_on_Ioi β)
  simpa [operatorPowerMean] using
    hconc (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) (θ := θ)
      (_root_.OperatorGeometricMean.pdSet_subset_psdSet (ℋ := ℋ) hA₁) (_root_.OperatorGeometricMean.pdSet_subset_psdSet (ℋ := ℋ) hA₂)
      hB₁ hB₂ hθ0 hθ1

/--
Theorem 1.1, convex range: the operator `(α, β)`-power mean is jointly convex on
strictly positive operators for `1 ≤ α ≤ 2` and `0 ≤ β ≤ 1`.
-/
theorem operatorPowerMean_jointlyConvexOn_pdSet
    {α β : ℝ}
    (hα : α ∈ Set.Icc (1 : ℝ) 2)
    (hβ : β ∈ Set.Icc (0 : ℝ) 1) :
    JointlyConvexOn (pdSet (ℋ := ℋ)) (pdSet (ℋ := ℋ))
      (operatorPowerMean (ℋ := ℋ) α β) := by
  intro A₁ A₂ B₁ B₂ θ hA₁ hA₂ hB₁ hB₂ hθ0 hθ1
  have hconv :=
    theorem_2_5_forward_jointlyConvexOn_psd_pd_Ici
      (ℋ := ℋ)
      (f := fun x : ℝ ↦ x ^ α)
      (h := fun x : ℝ ↦ x ^ β)
      (hf := by
        refine ⟨?_, ?_, ?_⟩
        · intro K _ _ _ _
          exact power_Icc_one_two_operatorConvexOn_Ici (ℋ := K) α hα
        · exact _root_.OperatorGeometricMean.rpow_continuousOn_Ici α (by linarith [hα.1])
        · have hα0 : α ≠ 0 := by linarith [hα.1]
          simp [Real.zero_rpow hα0]
      )
      (hconc := by
        exact _root_.OperatorGeometricMean.operatorConcaveOn_Ioi_of_Ici (ℋ := ℋ)
          (power_Icc_zero_one_operatorConcaveOn_Ici (ℋ := ℋ) β hβ))
      (hcont := by
        intro x hx
        exact (Real.continuousAt_rpow_const x β (Or.inl (ne_of_gt hx))).continuousWithinAt)
      (hpos := _root_.OperatorGeometricMean.rpow_pos_on_Ioi β)
  simpa [operatorPowerMean] using
    hconv (A₁ := A₁) (A₂ := A₂) (B₁ := B₁) (B₂ := B₂) (θ := θ)
      (_root_.OperatorGeometricMean.pdSet_subset_psdSet (ℋ := ℋ) hA₁) (_root_.OperatorGeometricMean.pdSet_subset_psdSet (ℋ := ℋ) hA₂)
      hB₁ hB₂ hθ0 hθ1

end OperatorGeometricMean


