-- Prove2me | Definitions.Def_CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_1
-- name    : CRCD_Quantum_TraceInequality_JensenOperatorInequalityIImpIV_part_1
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T23:59:05.694488+00:00
-- url     : https://prove2.me/theorems/3427ce1a-e589-4c0f-a26b-8779cec0bc93
-- title:
--   Contraction Jensen predicates and two-by-two operator identities
-- statement:
--   Let $H$ be a nontrivial complete complex Hilbert space, without a finite-dimensional restriction, and let $\mathcal L(H)$ denote bounded complex-linear operators. This part defines the single-contraction Jensen condition for a real function $f$: for self-adjoint $A$ with real spectrum in $[0,\infty)$ and $\|X\|\le1$,
--   $$
--   f(X^*AX)\le X^*f(A)X.
--   $$
--   It also defines the two-contraction condition, requiring the analogous inequality
--   $$
--   f(X^*AX+Y^*BY)\le X^*f(A)X+Y^*f(B)Y
--   $$
--   for self-adjoint $A,B$ with nonnegative spectra whenever $X^*X+Y^*Y\le1$. Here $f(A)$ is real continuous functional calculus. These are predicates; their truth is not assumed or proved by merely defining them. A third predicate packages operator convexity on $[0,\infty)$ uniformly over all nontrivial complete complex Hilbert spaces in the fixed universe, continuity of $f$ on that interval, and $f(0)\le0$.
--
--   The new technical interfaces work on the Hilbert direct sum $H\oplus H$. They define
--   $$
--   S_X=\begin{pmatrix}0&X^*\\X&0\end{pmatrix},\qquad
--   S_X^*=S_X,\qquad S_X^2=\operatorname{diag}(X^*X,XX^*),
--   $$
--   and prove $\|S_X\|\le1$ for contractions $X$, as well as $X^*X\le1$ and $XX^*\le1$. The part supplies block multiplication, addition and scalar-action identities, block-diagonal order compression and self-adjointness, the block-diagonal functional-calculus formula when $f$ is continuous on the union of the two spectra, and compatibility of positive square roots with block diagonals. It also proves $f(0\cdot1)=f(0)1$, unitary conjugation covariance under continuity on a set containing the spectrum, and auxiliary scalar/block identities used in the subsequent implication. Some purely algebraic helper statements omit completeness or nontriviality, as indicated in their formal types.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/TraceInequality/JensenOperatorInequalityIImpIV.lean#L28-L544

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
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzCore_part_3
import Definitions.Def_CRCD_Quantum_TraceInequality_LownerHeinzTheorem

/-
Copyright (c) 2025 Hayata Yamasaki. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors:
-/






set_option linter.style.longLine false

namespace JensenOperatorInequality

universe u

open LownerHeinzTheorem

section Theorem252

variable {ℋ : Type u}
variable [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ]
variable [Nontrivial ℋ]

set_option synthInstance.maxHeartbeats 400000 in
-- IsStarNormal CFC is only a theorem in Mathlib; CStarAlgebra chain through WithLp is deep.
noncomputable local instance : ContinuousFunctionalCalculus ℂ (L ℋ × L ℋ) IsStarNormal :=
  IsStarNormal.instContinuousFunctionalCalculus
set_option synthInstance.maxHeartbeats 400000 in
-- IsSelfAdjoint CFC for the product type, derived from IsStarNormal above.
noncomputable local instance : ContinuousFunctionalCalculus ℝ (L ℋ × L ℋ) IsSelfAdjoint :=
  IsSelfAdjoint.instContinuousFunctionalCalculus
set_option synthInstance.maxHeartbeats 400000 in
-- CStarAlgebra → NonnegSpectrumClass chain through WithLp is too deep for default heartbeats.
noncomputable local instance : NonnegSpectrumClass ℝ (L (HSum ℋ)) := inferInstance

/-- Condition (iv) in Theorem 2.5.2. -/
def CondIV (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A X : L ℋ⦄, IsSelfAdjoint A → spectrum ℝ A ⊆ Set.Ici (0 : ℝ) → ‖X‖ ≤ 1 →
    cfcR (ℋ := ℋ) f (star X * A * X) ≤ star X * cfcR (ℋ := ℋ) f A * X





omit ℋ [NormedAddCommGroup ℋ] [InnerProductSpace ℂ ℋ] [CompleteSpace ℋ] [Nontrivial ℋ] in
/--
Uniform localized version of Condition (i), packaged as
`OperatorConvexOnAll (Set.Ici 0)` together with continuity and `f 0 ≤ 0`.
-/
def CondIciAll (f : ℝ → ℝ) : Prop :=
  OperatorConvexOnAll.{u} (Set.Ici (0 : ℝ)) f ∧
    ContinuousOn f (Set.Ici (0 : ℝ)) ∧
    f 0 ≤ 0

/-- Condition (v) in Theorem 2.5.2. -/
def CondV (f : ℝ → ℝ) : Prop :=
  ∀ ⦃A B X Y : L ℋ⦄,
    IsSelfAdjoint A → IsSelfAdjoint B →
    spectrum ℝ A ⊆ Set.Ici (0 : ℝ) → spectrum ℝ B ⊆ Set.Ici (0 : ℝ) →
    star X * X + star Y * Y ≤ (1 : L ℋ) →
    cfcR (ℋ := ℋ) f (star X * A * X + star Y * B * Y) ≤
      star X * cfcR (ℋ := ℋ) f A * X + star Y * cfcR (ℋ := ℋ) f B * Y

/-- Selfadjoint `2 × 2` block built from a contraction candidate `X`. -/
 noncomputable def blockSwap (X : L ℋ) : L (HSum ℋ) :=
  blockOp (ℋ := ℋ) 0 (star X) X 0

omit [Nontrivial ℋ] in
 lemma blockSwap_star (X : L ℋ) :
    star (_root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X) = _root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X := by
  simp [_root_.JensenOperatorInequality.blockSwap, blockOp_star]

omit [Nontrivial ℋ] in
 lemma blockSwap_sq (X : L ℋ) :
    _root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X * _root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X =
      blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) := by
  ext z i
  fin_cases i <;>
    simp [_root_.JensenOperatorInequality.blockSwap, blockOp, blockDiagonal, ContinuousLinearMap.mul_def] <;> abel

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
 lemma blockDiagonal_eq_blockOp (A B : L ℋ) :
    blockDiagonal (ℋ := ℋ) A B = blockOp (ℋ := ℋ) A 0 0 B := by
  ext z i
  fin_cases i <;> simp [blockDiagonal, blockOp]

set_option maxHeartbeats 400000 in
-- Multiplying two generic `blockOp` expressions is elaboration-heavy.
omit [CompleteSpace ℋ] [Nontrivial ℋ] in
 lemma blockOp_mul (A00 A01 A10 A11 B00 B01 B10 B11 : L ℋ) :
    blockOp (ℋ := ℋ) A00 A01 A10 A11 * blockOp (ℋ := ℋ) B00 B01 B10 B11 =
      blockOp (ℋ := ℋ)
        (A00 * B00 + A01 * B10)
        (A00 * B01 + A01 * B11)
        (A10 * B00 + A11 * B10)
        (A10 * B01 + A11 * B11) := by
  -- The extra heartbeat budget stays local to this normalization lemma.
  refine blockOp_ext (ℋ := ℋ) ?_ ?_
  · intro z
    simp [ContinuousLinearMap.mul_def, add_left_comm, add_comm]
  · intro z
    simp [ContinuousLinearMap.mul_def, add_left_comm, add_comm]

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
 lemma blockOp_add
    (A00 A01 A10 A11 B00 B01 B10 B11 : L ℋ) :
    blockOp (ℋ := ℋ) A00 A01 A10 A11 + blockOp (ℋ := ℋ) B00 B01 B10 B11 =
      blockOp (ℋ := ℋ) (A00 + B00) (A01 + B01) (A10 + B10) (A11 + B11) := by
  ext z i
  fin_cases i <;> simp [blockOp] <;> abel

set_option synthInstance.maxHeartbeats 100000 in
-- Scalar action on `blockOp` triggers expensive instance search for nested operator expressions.
omit [Nontrivial ℋ] in
 lemma blockOp_smulR
    (r : ℝ) (A00 A01 A10 A11 : L ℋ) :
    r • blockOp (ℋ := ℋ) A00 A01 A10 A11 =
      blockOp (ℋ := ℋ) (r • A00) (r • A01) (r • A10) (r • A11) := by
  have coe_smul_hsum : ∀ (f : L (HSum ℋ)) (x : HSum ℋ), (r • f) x = r • (f x) := by
    intros; rfl
  have coe_smul_h : ∀ (f : L ℋ) (x : ℋ), (r • f) x = r • (f x) := by
    intros; rfl
  ext z i
  fin_cases i <;> {
    simp only [blockOp, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
      smul_add, coe_smul_hsum, coe_smul_h]
    simp [hsumProj, hsumIncl, hsumEquiv]
  }

omit [Nontrivial ℋ] in
 lemma blockSwap_add_I_smul_blockDiagonal (X R0 R1 : L ℋ) :
    _root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X + Complex.I • blockDiagonal (ℋ := ℋ) R0 R1 =
      blockOp (ℋ := ℋ) (Complex.I • R0) (star X) X (Complex.I • R1) := by
  rw [_root_.JensenOperatorInequality.blockDiagonal_eq_blockOp]
  ext z i
  fin_cases i <;> simp [_root_.JensenOperatorInequality.blockSwap, blockOp] <;> abel

omit [CompleteSpace ℋ] [Nontrivial ℋ] in
 lemma blockOp_mul_blockDiagonal_zero_right
    (P00 P01 P10 P11 A Q00 Q01 Q10 Q11 : L ℋ) :
    blockOp (ℋ := ℋ) P00 P01 P10 P11 * blockDiagonal (ℋ := ℋ) 0 A *
        blockOp (ℋ := ℋ) Q00 Q01 Q10 Q11 =
      blockOp (ℋ := ℋ)
        (P01 * A * Q10)
        (P01 * A * Q11)
        (P11 * A * Q10)
        (P11 * A * Q11) := by
  rw [_root_.JensenOperatorInequality.blockDiagonal_eq_blockOp, _root_.JensenOperatorInequality.blockOp_mul, _root_.JensenOperatorInequality.blockOp_mul]
  simp [mul_assoc, add_comm]

set_option synthInstance.maxHeartbeats 400000 in
-- `StarAlgHom.map_cfc` needs `MulAction ℝ (L (HSum ℋ))`; search is deep without section CFC.
omit [Nontrivial ℋ] in
 lemma cfcR_blockDiagonal (f : ℝ → ℝ)
    (A B : L ℋ) (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hcont : ContinuousOn f (spectrum ℝ A ∪ spectrum ℝ B)) :
    cfcR (ℋ := HSum ℋ) f (blockDiagonal (ℋ := ℋ) A B) =
      blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) := by
  let φ : (L ℋ × L ℋ) →⋆ₐ[ℝ] L (HSum ℋ) := blockDiagonalHom (ℋ := ℋ)
  have hφ : Continuous φ := by
    change Continuous (fun p : L ℋ × L ℋ => blockDiagonal (ℋ := ℋ) p.1 p.2)
    change Continuous (fun p : L ℋ × L ℋ =>
      hsumIncl ℋ 0 ∘L p.1 ∘L hsumProj ℋ 0 + hsumIncl ℋ 1 ∘L p.2 ∘L hsumProj ℋ 1)
    fun_prop
  have hpair : IsSelfAdjoint (A, B) := by
    change star (A, B) = (A, B)
    ext <;> simp [hA.star_eq, hB.star_eq]
  have hpair' : IsSelfAdjoint (φ (A, B)) := hpair.map φ
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := (A, B))
    (hf := by simpa [Prod.spectrum_eq] using hcont)
    (hφ := hφ) (ha := hpair) (hφa := hpair')
  have hprod :
      cfc (R := ℝ) (A := L ℋ × L ℋ) (p := IsSelfAdjoint) f (A, B) =
        (cfcR (ℋ := ℋ) f A, cfcR (ℋ := ℋ) f B) := by
    simpa [cfcR] using
      (cfc_map_prod (R := ℝ) (S := ℝ)
        (A := L ℋ) (B := L ℋ)
        (pab := IsSelfAdjoint) (pa := IsSelfAdjoint) (pb := IsSelfAdjoint)
        f A B
        (hf := hcont)
        (hab := hpair) (ha := hA) (hb := hB))
  calc
    cfcR (ℋ := HSum ℋ) f (blockDiagonal (ℋ := ℋ) A B)
        = cfc (R := ℝ) (A := L (HSum ℋ)) (p := IsSelfAdjoint) f (φ (A, B)) := by
          simp [cfcR, φ]
    _ = φ (cfc (R := ℝ) (A := L ℋ × L ℋ) (p := IsSelfAdjoint) f (A, B)) := by
          simpa using hmap.symm
    _ = φ (cfcR (ℋ := ℋ) f A, cfcR (ℋ := ℋ) f B) := by
          rw [hprod]
    _ = blockDiagonal (ℋ := ℋ) (cfcR (ℋ := ℋ) f A) (cfcR (ℋ := ℋ) f B) := by
          simp [φ, blockDiagonalHom]

-- Converting positivity on a block-diagonal operator to each diagonal block is expensive.
omit [Nontrivial ℋ] in
 lemma blockDiagonal_le_left {A0 A1 B0 B1 : L ℋ}
    (h : blockDiagonal (ℋ := ℋ) A0 A1 ≤ blockDiagonal (ℋ := ℋ) B0 B1) :
    A0 ≤ B0 := by
  have hnonneg : 0 ≤ blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1) := by
    have hsub :
        blockDiagonal (ℋ := ℋ) B0 B1 - blockDiagonal (ℋ := ℋ) A0 A1 =
          blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1) := by
      refine blockOp_ext (ℋ := ℋ) ?_ ?_
      · intro z
        simp [sub_eq_add_neg]
      · intro z
        simp [sub_eq_add_neg]
    exact hsub ▸ sub_nonneg.mpr h
  have hpos :
      (blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1)).IsPositive :=
    (ContinuousLinearMap.nonneg_iff_isPositive _).1 hnonneg
  have hleftPos : (B0 - A0).IsPositive := by
    rw [ContinuousLinearMap.isPositive_iff_complex]
    intro x
    have hx :=
      (ContinuousLinearMap.isPositive_iff_complex
        (blockDiagonal (ℋ := ℋ) (B0 - A0) (B1 - A1))).1 hpos (hsumIncl ℋ 0 x)
    simpa [blockDiagonal, hsumProj, hsumIncl, hsumEquiv, PiLp.inner_apply] using hx
  exact (sub_nonneg.mp ((ContinuousLinearMap.nonneg_iff_isPositive _).2 hleftPos))

omit [Nontrivial ℋ] in
 lemma blockDiagonal_selfAdjoint {A B : L ℋ}
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) :
    IsSelfAdjoint (blockDiagonal (ℋ := ℋ) A B) := by
  change star (blockDiagonal (ℋ := ℋ) A B) = blockDiagonal (ℋ := ℋ) A B
  simp [blockDiagonal_star, hA.star_eq, hB.star_eq]

omit [Nontrivial ℋ] in
 lemma cfcR_zero (f : ℝ → ℝ) :
    cfcR (ℋ := ℋ) f (0 : L ℋ) = algebraMap ℝ (L ℋ) (f 0) := by
  change cfc (R := ℝ) (A := L ℋ) (p := IsSelfAdjoint) f (0 : L ℋ) =
    algebraMap ℝ (L ℋ) (f 0)
  simp



omit [Nontrivial ℋ] in
 lemma cfcR_conj_unitary_on (s : Set ℝ) (f : ℝ → ℝ) (hcont : ContinuousOn f s)
    {A : L ℋ} (hAs : spectrum ℝ A ⊆ s)
    (u : unitary (L ℋ)) (hA : IsSelfAdjoint A) :
    cfcR (ℋ := ℋ) f (star u * A * u) = star u * cfcR (ℋ := ℋ) f A * u := by
  let φ : L ℋ →⋆ₐ[ℝ] L ℋ := Unitary.conjStarAlgAut ℝ (L ℋ) (star u)
  have hφ : Continuous φ := by
    have h1 : Continuous (fun x : L ℋ => (star u : L ℋ) * x * (u : L ℋ)) := by
      fun_prop
    have hEq : (fun x : L ℋ => φ x) = (fun x : L ℋ => (star u : L ℋ) * x * (u : L ℋ)) := by
      funext x
      simp [φ, Unitary.conjStarAlgAut_apply, mul_assoc]
    simpa [hEq] using h1
  have hφA : IsSelfAdjoint (φ A) := hA.map φ
  have hmap := StarAlgHom.map_cfc (φ := φ) (f := f) (a := A)
    (hf := hcont.mono hAs)
    (hφ := hφ) (ha := hA) (hφa := hφA)
  simpa [φ, cfcR, Unitary.conjStarAlgAut_apply, mul_assoc] using hmap.symm

omit [Nontrivial ℋ] in
 lemma cfcR_real_sqrt_eq_sqrt {A : L ℋ} (hA : (0 : L ℋ) ≤ A) :
    cfcR (ℋ := ℋ) Real.sqrt A = CFC.sqrt A := by
  rw [CFC.sqrt_eq_real_sqrt A hA, cfcₙ_eq_cfc (f := Real.sqrt) (a := A) (hf0 := by simp), cfcR]

omit [CompleteSpace ℋ] in
 theorem nontrivial_hsumL : Nontrivial (L (HSum ℋ)) := by
  have h_not_sub : ¬ Subsingleton ℋ := by
    intro hsub
    letI : Subsingleton ℋ := hsub
    letI : Subsingleton (L ℋ) := by infer_instance
    exact (not_nontrivial_iff_subsingleton.mpr (by infer_instance))
      (inferInstance : Nontrivial (L ℋ))
  have hH_nontriv : Nontrivial ℋ := (not_subsingleton_iff_nontrivial.mp h_not_sub)
  letI : Nontrivial ℋ := hH_nontriv
  rcases exists_pair_ne ℋ with ⟨x, y, hxy⟩
  let w : ℋ := x - y
  have hw : w ≠ 0 := sub_ne_zero.mpr hxy
  have hdiag_ne_zero : (blockDiagonal (ℋ := ℋ) (1 : L ℋ) 0 : L (HSum ℋ)) ≠ 0 := by
    intro h0
    have hz :
        blockDiagonal (ℋ := ℋ) (1 : L ℋ) 0 (hsumIncl ℋ 0 w) = 0 := by
      exact congrArg (fun T : L (HSum ℋ) => T (hsumIncl ℋ 0 w)) h0
    have hw0 : w = 0 := by
      have hz0 := congrArg (fun z : HSum ℋ => hsumProj ℋ 0 z) hz
      simpa [blockDiagonal] using hz0
    exact hw hw0
  exact ⟨0, blockDiagonal (ℋ := ℋ) (1 : L ℋ) 0, hdiag_ne_zero.symm⟩

set_option synthInstance.maxHeartbeats 100000 in
-- `CFC.sqrt` on block-diagonal operators triggers expensive instance search through the product map.
set_option linter.unusedSectionVars false in
set_option maxHeartbeats 400000 in
 lemma sqrt_blockDiagonal_of_nonneg
    {A B : L ℋ} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hA_nonneg : (0 : L ℋ) ≤ A) (hB_nonneg : (0 : L ℋ) ≤ B) :
    CFC.sqrt (blockDiagonal (ℋ := ℋ) A B) =
      blockDiagonal (ℋ := ℋ) (CFC.sqrt A) (CFC.sqrt B) := by
  letI : Algebra ℝ (L (HSum ℋ)) := by infer_instance
  letI : Nontrivial (L (HSum ℋ)) := _root_.JensenOperatorInequality.nontrivial_hsumL (ℋ := ℋ)
  have hdiag_nonneg : (0 : L (HSum ℋ)) ≤ blockDiagonal (ℋ := ℋ) A B :=
    blockDiagonal_nonneg (ℋ := ℋ) hA_nonneg hB_nonneg
  rw [← _root_.JensenOperatorInequality.cfcR_real_sqrt_eq_sqrt (ℋ := HSum ℋ) hdiag_nonneg]
  rw [_root_.JensenOperatorInequality.cfcR_blockDiagonal (ℋ := ℋ) (f := Real.sqrt) (A := A) (B := B) hA hB]
  · rw [← _root_.JensenOperatorInequality.cfcR_real_sqrt_eq_sqrt (ℋ := ℋ) hA_nonneg, ← _root_.JensenOperatorInequality.cfcR_real_sqrt_eq_sqrt (ℋ := ℋ) hB_nonneg]
  · simpa using
      (by cfc_cont_tac : ContinuousOn Real.sqrt (spectrum ℝ A ∪ spectrum ℝ B))

omit [Nontrivial ℋ] in
 lemma complex_I_smul_real_I_smul_invTwo (r : ℝ) (T : L ℋ) :
    Complex.I • r • Complex.I • (2⁻¹ : ℝ) • T =
      -((2⁻¹ : ℝ) * r) • T := by
  ext x
  have hcomm : r • (Complex.I • ((2⁻¹ : ℝ) • T x)) = Complex.I • (r • ((2⁻¹ : ℝ) • T x)) := by
    simpa using (smul_comm r (Complex.I : ℂ) ((2⁻¹ : ℝ) • T x))
  calc
    Complex.I • r • Complex.I • (2⁻¹ : ℝ) • T x
        = Complex.I • (r • (Complex.I • ((2⁻¹ : ℝ) • T x))) := by
            rfl
    _ = Complex.I • (Complex.I • (r • ((2⁻¹ : ℝ) • T x))) := by
            rw [hcomm]
    _ = ((Complex.I : ℂ) * Complex.I) • (r • ((2⁻¹ : ℝ) • T x)) := by
            rw [smul_smul]
    _ = (-1 : ℂ) • (r • ((2⁻¹ : ℝ) • T x)) := by
            norm_num
    _ = (-1 : ℂ) • (((r * 2⁻¹ : ℝ)) • T x) := by
            rw [smul_smul]
    _ = -((2⁻¹ : ℝ) * r) • T x := by
            simp [neg_smul, mul_comm]

omit [Nontrivial ℋ] in
 lemma real_smul_complex_I_real_smul_complex_I_comm (s r : ℝ) (T : L ℋ) :
    (s : ℝ) • Complex.I • r • Complex.I • T =
      Complex.I • r • Complex.I • (s : ℝ) • T := by
  calc
    (s : ℝ) • Complex.I • r • Complex.I • T
        = Complex.I • ((s : ℝ) • (r • (Complex.I • T))) := by
            simpa [smul_smul] using (smul_comm (s : ℝ) (Complex.I : ℂ) (r • (Complex.I • T)))
    _ = Complex.I • (r • ((s : ℝ) • (Complex.I • T))) := by
            rw [smul_comm (s : ℝ) r (Complex.I • T)]
    _ = Complex.I • (r • (Complex.I • ((s : ℝ) • T))) := by
            rw [smul_comm (s : ℝ) (Complex.I : ℂ) T]
    _ = Complex.I • r • Complex.I • (s : ℝ) • T := by
            rfl

omit [Nontrivial ℋ] in
 lemma half_add_half_eq (T : L ℋ) :
    (2⁻¹ : ℝ) • T + (2⁻¹ : ℝ) • T = T := by
  calc
    (2⁻¹ : ℝ) • T + (2⁻¹ : ℝ) • T = (2⁻¹ + 2⁻¹ : ℝ) • T := by
      simp [add_smul]
    _ = (1 : ℝ) • T := by norm_num
    _ = T := by simp

omit [Nontrivial ℋ] in
 lemma half_mul_real_add_half_mul_real_eq (r : ℝ) (T : L ℋ) :
    ((2⁻¹ : ℝ) * r) • T + ((2⁻¹ : ℝ) * r) • T = r • T := by
  calc
    ((2⁻¹ : ℝ) * r) • T + ((2⁻¹ : ℝ) * r) • T =
        (((2⁻¹ : ℝ) * r) + ((2⁻¹ : ℝ) * r)) • T := by
          simp [add_smul]
    _ = r • T := by ring_nf

omit [Nontrivial ℋ] in
 lemma rightEval_topLeft_scalar
    (r : ℝ) (R0 X T : L ℋ) :
    (2⁻¹ : ℝ) • (star X * (T * X)) +
        ((2⁻¹ : ℝ) • (star X * (T * X)) +
          (-((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
            -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)))) =
      star X * (T * X) + r • (R0 * R0) := by
  have hP :
      (2⁻¹ : ℝ) • (star X * (T * X)) +
          (2⁻¹ : ℝ) • (star X * (T * X)) =
        star X * (T * X) := by
    simpa using _root_.JensenOperatorInequality.half_add_half_eq (ℋ := ℋ) (star X * (T * X))
  have hQhalf :
      -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
          -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) =
        r • (R0 * R0) := by
    have hterm :
        -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) =
          ((2⁻¹ : ℝ) * r) • (R0 * R0) := by
      calc
        -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0))
            = -(Complex.I • r • Complex.I • (2⁻¹ : ℝ) • (R0 * R0)) := by
                rw [_root_.JensenOperatorInequality.real_smul_complex_I_real_smul_complex_I_comm
                  (ℋ := ℋ) (s := (2⁻¹ : ℝ)) (r := r) (T := R0 * R0)]
        _ = ((2⁻¹ : ℝ) * r) • (R0 * R0) := by
            rw [_root_.JensenOperatorInequality.complex_I_smul_real_I_smul_invTwo (ℋ := ℋ) (r := r) (T := R0 * R0)]
            simp
    calc
      -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
          -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) =
        ((2⁻¹ : ℝ) * r) • (R0 * R0) + ((2⁻¹ : ℝ) * r) • (R0 * R0) := by
          simp [hterm]
      _ = r • (R0 * R0) := _root_.JensenOperatorInequality.half_mul_real_add_half_mul_real_eq (ℋ := ℋ) r (R0 * R0)
  calc
    (2⁻¹ : ℝ) • (star X * (T * X)) +
        ((2⁻¹ : ℝ) • (star X * (T * X)) +
          (-((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
            -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0))))
        =
      ((2⁻¹ : ℝ) • (star X * (T * X)) +
          (2⁻¹ : ℝ) • (star X * (T * X))) +
        (-((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0)) +
          -((2⁻¹ : ℝ) • Complex.I • r • Complex.I • (R0 * R0))) := by
            abel
    _ = star X * (T * X) + r • (R0 * R0) := by rw [hP, hQhalf]

omit [Nontrivial ℋ] in
 lemma rightEval_bottomRight_scalar
    (r : ℝ) (R1 X T : L ℋ) :
    (2⁻¹ * r) • (X * star X) +
        ((2⁻¹ * r) • (X * star X) +
          ((2⁻¹ : ℝ) • (R1 * (T * R1)) +
            (2⁻¹ : ℝ) • (R1 * (T * R1)))) =
      (R1 * T * R1) + r • (X * star X) := by
  have hS :
      (2⁻¹ * r) • (X * star X) + (2⁻¹ * r) • (X * star X) = r • (X * star X) := by
    simpa using _root_.JensenOperatorInequality.half_mul_real_add_half_mul_real_eq (ℋ := ℋ) r (X * star X)
  have hT :
      (2⁻¹ : ℝ) • (R1 * (T * R1)) + (2⁻¹ : ℝ) • (R1 * (T * R1)) =
        R1 * (T * R1) := by
    simpa using _root_.JensenOperatorInequality.half_add_half_eq (ℋ := ℋ) (R1 * (T * R1))
  calc
    (2⁻¹ * r) • (X * star X) +
        ((2⁻¹ * r) • (X * star X) +
          ((2⁻¹ : ℝ) • (R1 * (T * R1)) +
            (2⁻¹ : ℝ) • (R1 * (T * R1))))
        =
      ((2⁻¹ * r) • (X * star X) + (2⁻¹ * r) • (X * star X)) +
        ((2⁻¹ : ℝ) • (R1 * (T * R1)) + (2⁻¹ : ℝ) • (R1 * (T * R1))) := by
            abel
    _ = r • (X * star X) + R1 * (T * R1) := by rw [hS, hT]
    _ = (R1 * T * R1) + r • (X * star X) := by simp [mul_assoc, add_comm]

 lemma star_mul_le_one (X : L ℋ) (hX : ‖X‖ ≤ 1) :
    (star X * X : L ℋ) ≤ 1 := by
  have h1 : star X * X ≤ algebraMap ℝ (L ℋ) (‖X‖ ^ 2) := by
    simpa [pow_two] using (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := X))
  have hsq : ‖X‖ ^ 2 ≤ 1 := by
    nlinarith [hX, norm_nonneg X]
  exact h1.trans (by simpa [Algebra.algebraMap_eq_smul_one] using hsq)

 lemma mul_star_le_one (X : L ℋ) (hX : ‖X‖ ≤ 1) :
    (X * star X : L ℋ) ≤ 1 := by
  have h1 : X * star X ≤ algebraMap ℝ (L ℋ) (‖X‖ ^ 2) := by
    simpa [pow_two] using (CStarAlgebra.star_mul_le_algebraMap_norm_sq (a := star X))
  have hsq : ‖X‖ ^ 2 ≤ 1 := by
    nlinarith [hX, norm_nonneg X]
  exact h1.trans (by simpa [Algebra.algebraMap_eq_smul_one] using hsq)

-- `simp` and normalization over block expressions are expensive here.
 lemma blockSwap_norm_le_one (X : L ℋ) (hX : ‖X‖ ≤ 1) :
    ‖_root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X‖ ≤ 1 := by
  have hSstar : star (_root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X) = _root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X :=
    _root_.JensenOperatorInequality.blockSwap_star (ℋ := ℋ) X
  have hSstarS :
      star (_root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X) * _root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X =
        blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) := by
    simpa [hSstar] using _root_.JensenOperatorInequality.blockSwap_sq (ℋ := ℋ) X
  have hDiagLe :
      blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) ≤ (1 : L (HSum ℋ)) := by
    have hA : 0 ≤ (1 : L ℋ) - star X * X := sub_nonneg.mpr (_root_.JensenOperatorInequality.star_mul_le_one (ℋ := ℋ) X hX)
    have hB : 0 ≤ (1 : L ℋ) - X * star X := sub_nonneg.mpr (_root_.JensenOperatorInequality.mul_star_le_one (ℋ := ℋ) X hX)
    have hnonneg : 0 ≤ blockDiagonal (ℋ := ℋ) (1 - star X * X) (1 - X * star X) :=
      blockDiagonal_nonneg (ℋ := ℋ) hA hB
    have hle :
        blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) ≤
          blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) +
            blockDiagonal (ℋ := ℋ) (1 - star X * X) (1 - X * star X) :=
      le_add_of_nonneg_right hnonneg
    have hsum :
        blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) +
          blockDiagonal (ℋ := ℋ) (1 - star X * X) (1 - X * star X) =
            blockDiagonal (ℋ := ℋ) (1 : L ℋ) (1 : L ℋ) := by
      refine blockOp_ext (ℋ := ℋ) ?_ ?_
      · intro z
        simp [sub_eq_add_neg, add_left_comm, add_comm]
      · intro z
        simp [sub_eq_add_neg, add_left_comm, add_comm]
    have hle' :
        blockDiagonal (ℋ := ℋ) (star X * X) (X * star X) ≤
          blockDiagonal (ℋ := ℋ) (1 : L ℋ) (1 : L ℋ) := by
      simpa [hsum] using hle
    simpa [blockDiagonal_one] using hle'
  have hSstarSle :
      star (_root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X) * _root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X ≤ (1 : L (HSum ℋ)) := by
    simpa [hSstarS] using hDiagLe
  have hSstarSnonneg : 0 ≤ star (_root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X) * _root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X := by
    exact star_mul_self_nonneg (_root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X)
  have hnormSq : ‖star (_root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X) * _root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X‖ ≤ 1 :=
    (CStarAlgebra.norm_le_one_iff_of_nonneg _ hSstarSnonneg).2 hSstarSle
  have hnormSq' : ‖_root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X‖ * ‖_root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X‖ ≤ 1 := by
    simpa [CStarRing.norm_star_mul_self] using hnormSq
  have hsq : ‖_root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X‖ ^ 2 ≤ 1 := by
    simpa [pow_two] using hnormSq'
  have hnonneg : 0 ≤ ‖_root_.JensenOperatorInequality.blockSwap (ℋ := ℋ) X‖ := norm_nonneg _
  nlinarith

 lemma continuousOn_union_of_subset_Ici {f : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ici (0 : ℝ))) {s t : Set ℝ}
    (hs : s ⊆ Set.Ici (0 : ℝ)) (ht : t ⊆ Set.Ici (0 : ℝ)) :
    ContinuousOn f (s ∪ t) := by
  refine hcont.mono ?_
  intro x hx
  rcases hx with hx | hx
  · exact hs hx
  · exact ht hx

omit [Nontrivial ℋ] in
 lemma spectrum_Ici_of_nonneg {A : L ℋ} (hA0 : (0 : L ℋ) ≤ A) :
    spectrum ℝ A ⊆ Set.Ici (0 : ℝ) := by
  exact
    (StarOrderedRing.nonneg_iff_spectrum_nonneg (R := ℝ) A
      (ha := IsSelfAdjoint.of_nonneg hA0)).1 hA0

 lemma spectrum_zero_subset_Ici :
    spectrum ℝ (0 : L ℋ) ⊆ Set.Ici (0 : ℝ) := by
  intro x hx
  have hx0 : x = 0 := by
    simpa using hx
  simp [Set.Ici, hx0]
end Theorem252
end JensenOperatorInequality


