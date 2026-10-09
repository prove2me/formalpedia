-- Prove2me | Definitions.Def_Nonadditivity_AdjointPurity
-- name    : Nonadditivity_AdjointPurity
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:19:59.7396+00:00
-- url     : https://prove2.me/theorems/84950af9-7236-431e-aca7-342943e44d6e
-- title:
--   Adjoint norm certificates imply output purity and entropy bounds
-- statement:
--   The Hilbert–Schmidt length of a complex matrix is $\sqrt{\operatorname{Re}\operatorname{tr}(A^*A)}$. Positive matrices have nonnegative trace pairings, and a density matrix evaluates a Hermitian observable at most at its operator norm. These facts convert an adjoint estimate on traceless Hermitian observables into a bound on the centered output state, hence into a purity upper bound and a von Neumann entropy lower bound. Entropies use natural logarithms.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/AdjointPurity.lean#L34-L154

import Definitions.Def_Nonadditivity_Entropy
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/








/-!
# Concrete state expectations and the adjoint-to-purity bridge

The norm on matrices in this file is the Euclidean operator norm. The
Hilbert--Schmidt length is defined by the actual matrix trace, independently
of the operator norm instance. The state expectation bound is proved from
positive semidefiniteness and trace normalization.
-/

noncomputable section

namespace Nonadditivity.AdjointPurity

open Nonadditivity.Entropy
open scoped Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator

set_option backward.isDefEq.respectTransparency false

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ]

/-- Even though a product of positive matrices need not be positive,
its trace is nonnegative. -/
theorem trace_mul_nonneg {A B : Matrix ι ι ℂ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  have hQ : (CFC.sqrt A).conjTranspose = CFC.sqrt A :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian.eq
  have htrace := (hB.conjTranspose_mul_mul_same (CFC.sqrt A)).trace_nonneg
  rw [Matrix.trace_mul_cycle, hQ, CFC.sqrt_mul_sqrt_self A hA.nonneg] at htrace
  exact htrace

/-- A normalized density matrix evaluates every Hermitian observable below
its operator norm. This supplies the missing input-state estimate. -/
theorem state_expectation_re_le_opNorm (ρ : DensityMatrix ι)
    (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    (ρ.matrix * A).trace.re ≤ ‖A‖ := by
  letI : CStarAlgebra (Matrix ι ι ℂ) := { }
  have hupper : A ≤ algebraMap ℝ (Matrix ι ι ℂ) ‖A‖ :=
    IsSelfAdjoint.le_algebraMap_norm_self (A := Matrix ι ι ℂ) hA.isSelfAdjoint
  have htrace := trace_mul_nonneg ρ.positive (Matrix.le_iff.mp hupper)
  have hscalar : (ρ.matrix * algebraMap ℝ (Matrix ι ι ℂ) ‖A‖).trace = (‖A‖ : ℂ) := by
    simp [Algebra.algebraMap_eq_smul_one, Matrix.trace_smul, ρ.normalized]
  have hre : 0 ≤ (ρ.matrix * (algebraMap ℝ (Matrix ι ι ℂ) ‖A‖ - A)).trace.re :=
    (RCLike.nonneg_iff.mp htrace).1
  rw [Matrix.mul_sub, Matrix.trace_sub, hscalar, Complex.sub_re, Complex.ofReal_re] at hre
  linarith







/-- The actual Hilbert--Schmidt length computed by matrix multiplication. -/
def hsLength (A : Matrix ι ι ℂ) : ℝ :=
  Real.sqrt ((A.conjTranspose * A).trace.re)

omit [DecidableEq ι] in
theorem hsLength_nonneg (A : Matrix ι ι ℂ) : 0 ≤ hsLength A :=
  Real.sqrt_nonneg _

omit [DecidableEq ι] in
theorem trace_conjTranspose_mul_self_re_nonneg (A : Matrix ι ι ℂ) :
    0 ≤ (A.conjTranspose * A).trace.re :=
  (RCLike.nonneg_iff.mp (Matrix.posSemidef_conjTranspose_mul_self A).trace_nonneg).1

omit [DecidableEq ι] in
theorem hsLength_sq (A : Matrix ι ι ℂ) :
    hsLength A ^ 2 = (A.conjTranspose * A).trace.re :=
  Real.sq_sqrt (trace_conjTranspose_mul_self_re_nonneg A)

omit [DecidableEq ι] in
theorem hsLength_sq_of_isHermitian (A : Matrix ι ι ℂ) (hA : A.IsHermitian) :
    hsLength A ^ 2 = (A * A).trace.re := by
  rw [hsLength_sq, hA.eq]

/-- The channel's matrix-trace adjoint certificate bounds the genuine
centered Hilbert--Schmidt length. The state expectation bound is a theorem
above, rather than an assumption in this statement. -/
theorem centered_hsLength_le_of_adjoint_certificate [Nonempty ι]
    (ρ : DensityMatrix κ) (Y : DensityMatrix ι)
    (adjoint : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) {t : ℝ} (ht : 0 ≤ t)
    (hhermitian : ∀ A, A.IsHermitian → (adjoint A).IsHermitian)
    (hduality : ∀ A, A.IsHermitian → A.trace = 0 →
      (Y.matrix * A).trace = (ρ.matrix * adjoint A).trace)
    (hcertificate : ∀ A, A.IsHermitian → A.trace = 0 →
      ‖adjoint A‖ ≤ t * hsLength A) : hsLength Y.centered ≤ t := by
  have hHerm := Y.centered_isHermitian
  have htrace := Y.centered_trace_zero
  have hsq : hsLength Y.centered ^ 2 ≤ t * hsLength Y.centered := by
    calc
      hsLength Y.centered ^ 2 = (Y.centered * Y.centered).trace.re :=
        hsLength_sq_of_isHermitian _ hHerm
      _ = (Y.matrix * Y.centered).trace.re := by rw [Y.centered_trace_pairing]
      _ = (ρ.matrix * adjoint Y.centered).trace.re := by rw [hduality _ hHerm htrace]
      _ ≤ ‖adjoint Y.centered‖ :=
        state_expectation_re_le_opNorm ρ _ (hhermitian _ hHerm)
      _ ≤ t * hsLength Y.centered := hcertificate _ hHerm htrace
  nlinarith [hsLength_nonneg Y.centered]

/-- Both conclusions of Lemma `purity`, from a concrete matrix-trace adjoint
relation and a genuine operator-to-Hilbert--Schmidt norm certificate. -/
theorem purity_and_entropy_of_adjoint_certificate [Nonempty ι]
    (ρ : DensityMatrix κ) (Y : DensityMatrix ι)
    (adjoint : Matrix ι ι ℂ →ₗ[ℂ] Matrix κ κ ℂ) {t : ℝ} (ht : 0 ≤ t)
    (hhermitian : ∀ A, A.IsHermitian → (adjoint A).IsHermitian)
    (hduality : ∀ A, A.IsHermitian → A.trace = 0 →
      (Y.matrix * A).trace = (ρ.matrix * adjoint A).trace)
    (hcertificate : ∀ A, A.IsHermitian → A.trace = 0 →
      ‖adjoint A‖ ≤ t * hsLength A) :
    Y.purity ≤ 1 / (Fintype.card ι : ℝ) + t ^ 2 ∧
      Real.log (Fintype.card ι) - Real.log (1 + (Fintype.card ι : ℝ) * t ^ 2) ≤
        Y.vonNeumann := by
  have hlength := centered_hsLength_le_of_adjoint_certificate ρ Y adjoint ht
    hhermitian hduality hcertificate
  apply Y.purity_and_entropy_of_centered_bound t
  rw [← hsLength_sq_of_isHermitian _ Y.centered_isHermitian]
  exact pow_le_pow_left₀ (hsLength_nonneg Y.centered) hlength 2



end Nonadditivity.AdjointPurity


