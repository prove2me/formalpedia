-- Prove2me | Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_1
-- name    : CRCD_Quantum_TraceInequality_LownerHeinzCore_part_1
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T22:50:05.638562+00:00
-- url     : https://prove2.me/theorems/ac50af8a-f14d-4129-8611-1998237ea6b9
-- title:
--   Operator convexity in an ordered C*-algebra and the inverse resolvent
-- statement:
--   Let $\mathcal A$ be a nontrivial complex C*-algebra equipped with its compatible partial order and star-ordered-ring structure. For a real function $f$, write $f(A)$ for the real continuous functional calculus on self-adjoint elements. This part defines operator convexity on a scalar set $S\subseteq\mathbb R$ by requiring, for self-adjoint $A,B$ whose real spectra lie in $S$ and for $0\le t\le1$,
--   $$
--   f((1-t)A+tB)\le(1-t)f(A)+tf(B).
--   $$
--   Operator concavity means operator convexity of $-f$. These are properties in the fixed ambient algebra; their definitions do not separately assume that $f$ is continuous or that $S$ is convex. Subsequent spectral and inequality results use the additional nonnegative-spectrum class linking the order to real spectra. No finite-dimensional hypothesis is required.
--
--   The part proves that $x\mapsto x^{-1}$ is operator convex on $(0,\infty)$, and that, for every real $a>0$, $x\mapsto(x+a)^{-1}$ is operator convex on $[0,\infty)$. Thus for positive operators $A,B$ and $0\le t\le1$, the shifted-resolvent inequality is
--   $$
--   \bigl((1-t)A+tB+a1\bigr)^{-1}
--    \le(1-t)(A+a1)^{-1}+t(B+a1)^{-1}.
--   $$
--   Supporting facts establish positivity of $TXT$ for $X\ge0$ and self-adjoint $T$, preservation of strictly positive spectra by convex combinations, positivity of the two-by-two block $\begin{pmatrix}A&1\\1&A^{-1}\end{pmatrix}$ when $A$ is self-adjoint with spectrum in $(0,\infty)$, and the corresponding Schur-complement conjugation identity. All inverse expressions in these conclusions are taken on spectra where the stated hypotheses make them nonsingular.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/TraceInequality/LownerHeinzCore.lean#L25-L653

import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/





set_option linter.style.longLine false

namespace LownerHeinzCore

universe u v

open CFC

section Pure

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]

noncomputable abbrev cfcR (f : ℝ → ℝ) (A : 𝓐) : 𝓐 :=
  cfc (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) f A











/-- Fixed-space operator convexity on `s` for the ambient algebra `𝓐`. -/
def OperatorConvexOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B : 𝓐⦄ ⦃t : ℝ⦄,
    IsSelfAdjoint A → IsSelfAdjoint B →
    0 ≤ t → t ≤ 1 →
    spectrum ℝ A ⊆ s → spectrum ℝ B ⊆ s →
    cfcR f ((1 - t) • A + t • B)
      ≤ (1 - t) • cfcR f A + t • cfcR f B



/-- Fixed-space operator concavity on `s` for the ambient algebra `𝓐`. -/
def OperatorConcaveOn (s : Set ℝ) (f : ℝ → ℝ) : Prop :=
  OperatorConvexOn (𝓐 := 𝓐) (s : Set ℝ) (fun x => - f x)

















end Pure

section Spectrum

variable {𝓐 : Type u}
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐]
variable [Nontrivial 𝓐]
variable [NonnegSpectrumClass ℝ 𝓐]

omit [Nontrivial (𝓐)] [NonnegSpectrumClass ℝ 𝓐] in
lemma conjugate_isPositive {X T : 𝓐} (hX : 0 ≤ X) (hT : IsSelfAdjoint T) :
    0 ≤ T * X * T := by
  simpa using hT.conjugate_nonneg hX



 lemma spectrum_convexCombo_Ioi {A B : 𝓐} {t : ℝ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (As : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) (Bs : spectrum ℝ B ⊆ Set.Ioi (0 : ℝ)) :
    spectrum ℝ ((1 - t) • A + t • B) ⊆ Set.Ioi (0 : ℝ) := by
  set C : 𝓐 := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
  have hApos : ∃ r > 0, algebraMap ℝ (𝓐) r ≤ A := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := 𝓐) (a := A) (ha := hA)).2 ?_
    intro x hx
    exact As hx
  have hBpos : ∃ r > 0, algebraMap ℝ (𝓐) r ≤ B := by
    refine (CFC.exists_pos_algebraMap_le_iff (A := 𝓐) (a := B) (ha := hB)).2 ?_
    intro x hx
    exact Bs hx
  rcases hApos with ⟨rA, hrA, hrA_le⟩
  rcases hBpos with ⟨rB, hrB, hrB_le⟩
  set rC : ℝ := (1 - t) * rA + t * rB
  have hrC : 0 < rC := by
    by_cases h1t : (1 - t) = 0
    · have ht' : t = 1 := by simpa [sub_eq_zero] using (sub_eq_zero.mp h1t).symm
      subst ht'
      simpa [rC, h1t] using hrB
    · simpa [rC] using add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne' (sub_nonneg.mpr ht1) (by simpa using h1t)) hrA) (mul_nonneg ht0 (le_of_lt hrB))
  have hrC_le : algebraMap ℝ (𝓐) rC ≤ C := by
    have hsum : (1 - t) • algebraMap ℝ (𝓐) rA + t • algebraMap ℝ (𝓐) rB ≤ C := by
      simpa [C] using add_le_add (smul_le_smul_of_nonneg_left hrA_le (sub_nonneg.mpr ht1)) (smul_le_smul_of_nonneg_left hrB_le ht0)
    have hLHS :
        (1 - t) • algebraMap ℝ (𝓐) rA + t • algebraMap ℝ (𝓐) rB =
          algebraMap ℝ (𝓐) rC := by
      simp [rC, Algebra.smul_def]
    simpa [hLHS] using hsum
  intro x hx
  simpa [C] using (CFC.exists_pos_algebraMap_le_iff (A := 𝓐) (a := C) (ha := hC)).1 ⟨rC, hrC, hrC_le⟩ x hx

omit [Nontrivial (𝓐)] in
omit [NonnegSpectrumClass ℝ 𝓐] in
 lemma posSemidef_block_one_inv {A : 𝓐} (hA : IsSelfAdjoint A)
    (As : spectrum ℝ A ⊆ Set.Ioi (0 : ℝ)) :
    Matrix.PosSemidef
      (!![A, 1; 1, cfcR (fun x : ℝ ↦ x⁻¹) A] : Matrix (Fin 2) (Fin 2) 𝓐) := by
  -- Gram matrix construction using `A^{1/2}` and `A^{-1/2}`
  set sqrtA : 𝓐 := cfcR (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) A
  set invSqrtA : 𝓐 := cfcR (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) A
  set v : Fin 2 → 𝓐 := fun i => if i = 0 then sqrtA else invSqrtA
  have posV : Matrix.PosSemidef (Matrix.vecMulVec v (star v)) := by
    simpa using (Matrix.posSemidef_vecMulVec_self_star (R := 𝓐) v)
  have hsqrtA : IsSelfAdjoint sqrtA := by
    dsimp [sqrtA, cfcR]
    exact cfc_predicate _ _
  have hinvSqrtA : IsSelfAdjoint invSqrtA := by
    dsimp [invSqrtA, cfcR]
    exact cfc_predicate _ _
  have hcont_sqrt : ContinuousOn (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2)) (spectrum ℝ A) :=
    fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt (As hx)))).continuousWithinAt
  have hcont_invSqrt : ContinuousOn (fun x : ℝ ↦ x ^ ((-1 : ℝ) / 2)) (spectrum ℝ A) :=
    fun x hx => (Real.continuousAt_rpow_const x _ (Or.inl (ne_of_gt (As hx)))).continuousWithinAt
  have sqrtA_mul_invSqrtA : sqrtA * invSqrtA = (1 : 𝓐) := by
    dsimp [sqrtA, invSqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_sqrt hcont_invSqrt, ← cfc_const_one ℝ A]
    apply cfc_congr
    intro x hx
    dsimp only
    rw [← Real.rpow_add (As hx), show ((1 : ℝ) / 2 + (-1) / 2 : ℝ) = 0 from by ring, Real.rpow_zero]
  have invSqrtA_mul_sqrtA : invSqrtA * sqrtA = (1 : 𝓐) := by
    dsimp [sqrtA, invSqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_invSqrt hcont_sqrt, ← cfc_const_one ℝ A]
    apply cfc_congr
    intro x hx
    dsimp only
    rw [← Real.rpow_add (As hx), show ((-1 : ℝ) / 2 + (1 : ℝ) / 2 : ℝ) = 0 from by ring, Real.rpow_zero]
  have invSqrtA_mul_invSqrtA : invSqrtA * invSqrtA = cfcR (fun x : ℝ ↦ x ^ (-1 : ℝ)) A := by
    dsimp [invSqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_invSqrt hcont_invSqrt]
    apply cfc_congr
    intro x hx
    dsimp only
    rw [← Real.rpow_add (As hx), show ((-1 : ℝ) / 2 + (-1 : ℝ) / 2 : ℝ) = -1 from by ring]
  have sqrtA_mul_sqrtA : sqrtA * sqrtA = A := by
    dsimp [sqrtA, cfcR]
    rw [← cfc_mul _ _ A hcont_sqrt hcont_sqrt]
    calc
      cfcR (fun x : ℝ ↦ x ^ ((1 : ℝ) / 2) * x ^ ((1 : ℝ) / 2)) A =
          cfcR (fun x : ℝ ↦ x) A := by
            apply cfc_congr
            intro x hx
            dsimp only
            rw [← Real.rpow_add (As hx), show ((1 : ℝ) / 2 + (1 : ℝ) / 2 : ℝ) = 1 from by ring, Real.rpow_one]
      _ = A := cfc_id' (R := ℝ) (a := A) (ha := hA)
  have invA_eq : cfcR (fun x : ℝ ↦ x ^ (-1 : ℝ)) A = cfcR (fun x : ℝ ↦ x⁻¹) A := by
    dsimp [cfcR]
    apply cfc_congr
    intro x hx
    have hxne : x ≠ 0 := ne_of_gt (As hx)
    simpa [hxne] using (Real.rpow_neg_one x)
  have hEq : Matrix.vecMulVec v (star v) = (!![A, 1; 1, cfcR (fun x : ℝ ↦ x⁻¹) A] :
      Matrix (Fin 2) (Fin 2) (𝓐)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.vecMulVec_apply, v, hsqrtA.star_eq, hinvSqrtA.star_eq, sqrtA_mul_sqrtA,
        sqrtA_mul_invSqrtA, invSqrtA_mul_sqrtA, invSqrtA_mul_invSqrtA, invA_eq]
  simpa [hEq] using posV

omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
 lemma schur_conj_eq_diagonal {C D invC : 𝓐} (hInvC_sa : IsSelfAdjoint invC)
    (invC_mul_C : invC * C = (1 : 𝓐)) (C_mul_invC : C * invC = (1 : 𝓐)) :
    star (!![(1 : 𝓐), -invC; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓐))
        * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐))
        * (!![(1 : 𝓐), -invC; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓐))
      = Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC) := by
  set U : Matrix (Fin 2) (Fin 2) (𝓐) := !![(1 : 𝓐), -invC; 0, 1]
  have hstarU : star U = !![(1 : 𝓐), 0; -invC, 1] := by
    dsimp [U]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hInvC_sa.star_eq]
  have hP :
      star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) =
        !![C, 1; -invC * C + 1, -invC + D] := by
    simp [hstarU, U]
  have hQ :
      star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U =
        !![C, 0; 0, D - invC] := by
    have hstep :
        star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U =
          (!![C, 1; -invC * C + 1, -invC + D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U := by
      simpa [mul_assoc] using congrArg (fun X => X * U) hP
    dsimp [U] at hstep ⊢
    simp [hstep, C_mul_invC, invC_mul_C, sub_eq_add_neg, add_comm]
  have hdiag :
      (Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC)) =
        (!![C, 0; 0, D - invC] : Matrix (Fin 2) (Fin 2) (𝓐)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  simpa [hdiag] using hQ

theorem one_div_operatorConvexOn_Ioi :
  OperatorConvexOn (𝓐 := 𝓐) (Set.Ioi (0 : ℝ)) (fun x : ℝ ↦ 1 / x) := by
  dsimp [OperatorConvexOn]
  intro A B t hA hB ht0 ht1 As Bs
  -- rewrite `1/x` as `x⁻¹`
  simp only [one_div]
  set C : 𝓐 := (1 - t) • A + t • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - t)).smul hA |>.add ((IsSelfAdjoint.all t).smul hB)
  have specC : spectrum ℝ C ⊆ Set.Ioi (0 : ℝ) := by
    simpa [C] using
      _root_.LownerHeinzCore.spectrum_convexCombo_Ioi  (A := A) (B := B) (t := t) hA hB ht0 ht1 As Bs
  set invA : 𝓐 := cfcR (fun x : ℝ ↦ x⁻¹) A
  set invB : 𝓐 := cfcR (fun x : ℝ ↦ x⁻¹) B
  set invC : 𝓐 := cfcR (fun x : ℝ ↦ x⁻¹) C
  set D : 𝓐 := (1 - t) • invA + t • invB
  let M_A : Matrix (Fin 2) (Fin 2) (𝓐) := !![A, 1; 1, invA]
  let M_B : Matrix (Fin 2) (Fin 2) (𝓐) := !![B, 1; 1, invB]
  let M : Matrix (Fin 2) (Fin 2) (𝓐) := (1 - t) • M_A + t • M_B
  have posA : Matrix.PosSemidef M_A := by
    simpa [M_A, invA] using _root_.LownerHeinzCore.posSemidef_block_one_inv  (A := A) hA As
  have posB : Matrix.PosSemidef M_B := by
    simpa [M_B, invB] using _root_.LownerHeinzCore.posSemidef_block_one_inv  (A := B) hB Bs
  have posM : Matrix.PosSemidef M := by
    simpa [M] using Matrix.PosSemidef.add
      (Matrix.PosSemidef.smul (x := M_A) (a := (1 - t)) posA (sub_nonneg.mpr ht1))
      (Matrix.PosSemidef.smul (x := M_B) (a := t) posB ht0)
  have hM : M = !![C, 1; 1, D] := by
    ext i j
    fin_cases i <;> fin_cases j
    · simp [M, M_A, M_B, C]
    · have h1 : (1 - t) • (1 : 𝓐) + t • (1 : 𝓐) = (1 : 𝓐) := by
        calc
          (1 - t) • (1 : 𝓐) + t • (1 : 𝓐) = ((1 - t) + t) • (1 : 𝓐) := by
            simpa using (add_smul (1 - t) t (1 : 𝓐)).symm
          _ = (1 : 𝓐) := by simp [sub_add_cancel]
      simp [M, M_A, M_B, h1]
    · have h1 : (1 - t) • (1 : 𝓐) + t • (1 : 𝓐) = (1 : 𝓐) := by
        calc
          (1 - t) • (1 : 𝓐) + t • (1 : 𝓐) = ((1 - t) + t) • (1 : 𝓐) := by
            simpa using (add_smul (1 - t) t (1 : 𝓐)).symm
          _ = (1 : 𝓐) := by simp [sub_add_cancel]
      simp [M, M_A, M_B, h1]
    · simp [M, M_A, M_B, D]
  let U : Matrix (Fin 2) (Fin 2) (𝓐) := !![(1 : 𝓐), -invC; 0, 1]
  have hU : IsUnit U := by
    let V : Matrix (Fin 2) (Fin 2) (𝓐) := !![(1 : 𝓐), invC; 0, 1]
    refine ⟨⟨U, V, ?_, ?_⟩, rfl⟩
    · dsimp [U, V]
      simp [Matrix.one_fin_two]
    · dsimp [U, V]
      simp [Matrix.one_fin_two]
  have hconj :
      star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U
        = Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC) := by
    have hInvC_sa : IsSelfAdjoint invC := by
      dsimp [invC, cfcR]
      exact cfc_predicate _ _
    have hcont_inv : ContinuousOn (fun x : ℝ ↦ x⁻¹) (spectrum ℝ C) :=
      fun x hx => (continuousAt_inv₀ (ne_of_gt (specC hx))).continuousWithinAt
    have invC_mul_C : invC * C = (1 : 𝓐) := by
      dsimp [invC, cfcR]
      have hmul :
          cfcR (fun x : ℝ ↦ x⁻¹) C * C =
            cfcR (fun x : ℝ ↦ x⁻¹ * x) C := by
        simpa [cfc_id' (R := ℝ) (a := C) (ha := hC)] using
          (cfc_mul (fun x : ℝ ↦ x⁻¹) (fun x : ℝ ↦ x) C hcont_inv continuousOn_id).symm
      rw [hmul, ← cfc_const_one ℝ C]
      apply cfc_congr
      intro x hx
      have hxne : x ≠ 0 := ne_of_gt (specC hx)
      simp [hxne]
    have C_mul_invC : C * invC = (1 : 𝓐) := by
      dsimp [invC, cfcR]
      have hmul :
          C * cfcR (fun x : ℝ ↦ x⁻¹) C =
            cfcR (fun x : ℝ ↦ x * x⁻¹) C := by
        simpa [cfc_id' (R := ℝ) (a := C) (ha := hC)] using
          (cfc_mul (fun x : ℝ ↦ x) (fun x : ℝ ↦ x⁻¹) C continuousOn_id hcont_inv).symm
      rw [hmul, ← cfc_const_one ℝ C]
      apply cfc_congr
      intro x hx
      have hxne : x ≠ 0 := ne_of_gt (specC hx)
      simp [hxne]
    simpa [U] using
      _root_.LownerHeinzCore.schur_conj_eq_diagonal  (C := C) (D := D) (invC := invC)
        hInvC_sa invC_mul_C C_mul_invC
  have posDiag :
      Matrix.PosSemidef (Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC)) := by
    have posConj : Matrix.PosSemidef (star U * M * U) := by
      simpa [Matrix.star_eq_conjTranspose] using (posM.conjTranspose_mul_mul_same U)
    have posConj' :
        Matrix.PosSemidef
          (star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) 𝓐) * U) := by
      -- rewrite the middle block matrix as `M`
      rw [← hM]
      exact posConj
    -- rewrite the goal using the computed conjugation
    rw [← hconj]
    exact posConj'
  have hinvC : invC ≤ D := by
    have hDinvC : 0 ≤ D - invC := by
      simpa using
        (Matrix.posSemidef_diagonal_iff (R := 𝓐)
          (d := fun i : Fin 2 => if i = 0 then C else D - invC)).1 posDiag (1 : Fin 2)
    exact le_of_sub_nonneg hDinvC
  exact hinvC



-- Reduces to `one_div_operatorConvexOn_Ioi` and is also elaboration-heavy.
theorem one_div_add_t_operatorConvexOn_Ici : ∀ (t : ℝ), 0 < t →
  OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  /-
  It follows from one_div_operatorConvexOn_Ioi
  -/
  intro t ht
  dsimp [OperatorConvexOn]
  intro A B θ hA hB hθ0 hθ1 As Bs
  -- rewrite `1 / (x + t)` as `(x + t)⁻¹` for `simp`/`cfc` lemmas
  simp only [one_div]
  -- Reduce to operator convexity of `x ↦ x⁻¹` on `Ioi 0` by shifting by `t`.
  set C : 𝓐 := (1 - θ) • A + θ • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - θ)).smul hA |>.add ((IsSelfAdjoint.all θ).smul hB)
  set shift : ℝ → ℝ := fun x ↦ x + t
  set T : 𝓐 := algebraMap ℝ (𝓐) t
  have hT : IsSelfAdjoint T := by
    simpa [T] using (IsSelfAdjoint.algebraMap (A := 𝓐) (r := t)
      (hr := IsSelfAdjoint.all (t : ℝ)))
  have A_nonneg : 0 ≤ A := by
    have h0 : 0 ≤ cfcR (fun x : ℝ ↦ x) A := by
      dsimp [cfcR]
      apply cfc_nonneg
      intro x hx
      simpa [Set.Ici] using (As hx)
    simpa [cfcR, cfc_id' (R := ℝ) (a := A) (ha := hA)] using h0
  have B_nonneg : 0 ≤ B := by
    have h0 : 0 ≤ cfcR (fun x : ℝ ↦ x) B := by
      dsimp [cfcR]
      apply cfc_nonneg
      intro x hx
      simpa [Set.Ici] using (Bs hx)
    simpa [cfcR, cfc_id' (R := ℝ) (a := B) (ha := hB)] using h0
  have C_nonneg : 0 ≤ C := by
    simpa [C] using add_nonneg (smul_nonneg (sub_nonneg.mpr hθ1) A_nonneg) (smul_nonneg hθ0 B_nonneg)
  have hA_shift : cfcR shift A = A + T := by
    dsimp [cfcR, shift, T]
    simpa [cfc_id' (R := ℝ) (a := A) (ha := hA)] using
      (cfc_add_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t)
        (f := fun x : ℝ ↦ x) (a := A) (ha := hA))
  have hB_shift : cfcR shift B = B + T := by
    dsimp [cfcR, shift, T]
    simpa [cfc_id' (R := ℝ) (a := B) (ha := hB)] using
      (cfc_add_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t)
        (f := fun x : ℝ ↦ x) (a := B) (ha := hB))
  have hC_shift : cfcR shift C = C + T := by
    dsimp [cfcR, shift, T]
    simpa [cfc_id' (R := ℝ) (a := C) (ha := hC)] using
      (cfc_add_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t)
        (f := fun x : ℝ ↦ x) (a := C) (ha := hC))
  set A1 : 𝓐 := A + T
  set B1 : 𝓐 := B + T
  set C1 : 𝓐 := (1 - θ) • A1 + θ • B1
  have hA1_sa : IsSelfAdjoint A1 := by
    subst A1
    exact hA.add hT
  have hB1_sa : IsSelfAdjoint B1 := by
    subst B1
    exact hB.add hT
  have specA1 : spectrum ℝ A1 ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    have hs : spectrum ℝ (cfc shift A) = shift '' spectrum ℝ A := by
      simpa [shift] using
        (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := A)
          (f := shift) (ha := hA))
    have hx' : x ∈ shift '' spectrum ℝ A := by
      have hx0 : x ∈ spectrum ℝ (cfc shift A) := by
        have hval : cfc shift A = A1 := by
          simpa [cfcR, shift, A1] using hA_shift
        simpa [hval] using hx
      simpa [hs] using hx0
    rcases hx' with ⟨y, hy, rfl⟩
    have hy0 : 0 ≤ y := by
      simpa [Set.Ici] using (As hy)
    simpa [Set.Ioi] using (add_pos_of_nonneg_of_pos hy0 ht)
  have specB1 : spectrum ℝ B1 ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    have hs : spectrum ℝ (cfc shift B) = shift '' spectrum ℝ B := by
      simpa [shift] using
        (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := B)
          (f := shift) (ha := hB))
    have hx' : x ∈ shift '' spectrum ℝ B := by
      have hx0 : x ∈ spectrum ℝ (cfc shift B) := by
        have hval : cfc shift B = B1 := by
          simpa [cfcR, shift, B1] using hB_shift
        simpa [hval] using hx
      simpa [hs] using hx0
    rcases hx' with ⟨y, hy, rfl⟩
    have hy0 : 0 ≤ y := by
      simpa [Set.Ici] using (Bs hy)
    simpa [Set.Ioi] using (add_pos_of_nonneg_of_pos hy0 ht)
  have hC1 : C1 = C + T := by
    subst A1 B1 C1
    simp [C, add_assoc, add_left_comm, add_comm, smul_add]
  have hshift_ne0_A : ∀ x ∈ spectrum ℝ A, shift x ≠ 0 := by
    intro x hx
    have hx0 : 0 ≤ x := by
      simpa [Set.Ici] using (As hx)
    exact ne_of_gt (by simpa [shift] using (add_pos_of_nonneg_of_pos hx0 ht))
  have hshift_ne0_B : ∀ x ∈ spectrum ℝ B, shift x ≠ 0 := by
    intro x hx
    have hx0 : 0 ≤ x := by
      simpa [Set.Ici] using (Bs hx)
    exact ne_of_gt (by simpa [shift] using (add_pos_of_nonneg_of_pos hx0 ht))
  have hshift_ne0_C : ∀ x ∈ spectrum ℝ C, shift x ≠ 0 :=
    fun x hx ↦ ne_of_gt (by simpa [shift] using (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg C_nonneg hx) ht))
  have hA_inv : cfcR (fun x : ℝ ↦ (x + t)⁻¹) A = Ring.inverse A1 := by
    have h' : cfc (fun x : ℝ ↦ (shift x)⁻¹) A = Ring.inverse (cfc shift A) := by
      simpa [shift] using (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := shift) (a := A) hshift_ne0_A (ha := hA))
    have hval : cfc shift A = A1 := by
      simpa [cfcR, shift, A1] using hA_shift
    simpa [cfcR, shift, hval] using h'
  have hB_inv : cfcR (fun x : ℝ ↦ (x + t)⁻¹) B = Ring.inverse B1 := by
    have h' : cfc (fun x : ℝ ↦ (shift x)⁻¹) B = Ring.inverse (cfc shift B) := by
      simpa [shift] using (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := shift) (a := B) hshift_ne0_B (ha := hB))
    have hval : cfc shift B = B1 := by
      simpa [cfcR, shift, B1] using hB_shift
    simpa [cfcR, shift, hval] using h'
  have hC_inv : cfcR (fun x : ℝ ↦ (x + t)⁻¹) C = Ring.inverse (C + T) := by
    have h' : cfc (fun x : ℝ ↦ (shift x)⁻¹) C = Ring.inverse (cfc shift C) := by
      simpa [shift] using (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := shift) (a := C) hshift_ne0_C (ha := hC))
    have hval : cfc shift C = C + T := by
      simpa [cfcR, shift] using hC_shift
    simpa [cfcR, shift, hval] using h'
  have hA1_inv : cfcR (fun x : ℝ ↦ x⁻¹) A1 = Ring.inverse A1 := by
    dsimp [cfcR]
    simpa [cfc_id' (R := ℝ) (a := A1) (ha := hA1_sa)] using
      (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x)
        (a := A1) (fun x hx ↦ ne_of_gt (specA1 hx)) (ha := hA1_sa))
  have hB1_inv : cfcR (fun x : ℝ ↦ x⁻¹) B1 = Ring.inverse B1 := by
    dsimp [cfcR]
    simpa [cfc_id' (R := ℝ) (a := B1) (ha := hB1_sa)] using
      (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x)
        (a := B1) (fun x hx ↦ ne_of_gt (specB1 hx)) (ha := hB1_sa))
  have hA_eq : cfcR (fun x : ℝ ↦ (x + t)⁻¹) A = cfcR (fun x : ℝ ↦ x⁻¹) A1 := by
    simp [hA_inv, hA1_inv]
  have hB_eq : cfcR (fun x : ℝ ↦ (x + t)⁻¹) B = cfcR (fun x : ℝ ↦ x⁻¹) B1 := by
    simp [hB_inv, hB1_inv]
  have specC1 : spectrum ℝ C1 ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    have hs : spectrum ℝ (cfc shift C) = shift '' spectrum ℝ C := by
      simpa [shift] using
        (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := C)
          (f := shift) (ha := hC))
    have hx' : x ∈ shift '' spectrum ℝ C := by
      have hx0 : x ∈ spectrum ℝ (cfc shift C) := by
        have hval : cfc shift C = C + T := by
          simpa [cfcR, shift] using hC_shift
        have hval' : cfc shift C = C1 := by
          simpa [hC1] using hval
        simpa [hval'] using hx
      simpa [hs] using hx0
    rcases hx' with ⟨y, hy, rfl⟩
    have hy0 : 0 ≤ y := spectrum_nonneg_of_nonneg C_nonneg hy
    have : 0 < y + t := add_pos_of_nonneg_of_pos hy0 ht
    simpa [Set.Ioi] using this
  have hC1_ne0 : ∀ x ∈ spectrum ℝ C1, (x : ℝ) ≠ 0 := fun x hx ↦ ne_of_gt (specC1 hx)
  have hC1_sa : IsSelfAdjoint C1 := by
    simpa [hC1] using (hC.add hT)
  have hC1_inv : cfcR (fun x : ℝ ↦ x⁻¹) C1 = Ring.inverse C1 := by
    dsimp [cfcR]
    simpa [cfc_id' (R := ℝ) (a := C1) (ha := hC1_sa)] using
      (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x)
        (a := C1) hC1_ne0 (ha := hC1_sa))
  have hC_eq : cfcR (fun x : ℝ ↦ (x + t)⁻¹) C = cfcR (fun x : ℝ ↦ x⁻¹) C1 := by
    calc
      cfcR (fun x : ℝ ↦ (x + t)⁻¹) C
          = Ring.inverse (C + T) := hC_inv
      _ = Ring.inverse C1 := by simp [hC1]
      _ = cfcR (fun x : ℝ ↦ x⁻¹) C1 := by simpa using hC1_inv.symm
  have hconv :
      cfcR (fun x : ℝ ↦ x⁻¹) C1
        ≤ (1 - θ) • cfcR (fun x : ℝ ↦ x⁻¹) A1
          + θ • cfcR (fun x : ℝ ↦ x⁻¹) B1 := by
    simpa [one_div] using
      (one_div_operatorConvexOn_Ioi  (A := A1) (B := B1) (t := θ)
        hA1_sa hB1_sa hθ0 hθ1 specA1 specB1)
  -- conclude by rewriting everything to the shifted `1/x` convexity statement
  simpa [C, hC_eq, hA_eq, hB_eq] using hconv
end Spectrum
end LownerHeinzCore


