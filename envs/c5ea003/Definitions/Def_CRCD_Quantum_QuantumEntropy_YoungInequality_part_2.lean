-- Prove2me | Definitions.Def_CRCD_Quantum_QuantumEntropy_YoungInequality_part_2
-- name    : CRCD_Quantum_QuantumEntropy_YoungInequality_part_2
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-08T00:00:59.360439+00:00
-- url     : https://prove2.me/theorems/38aaa8d2-a267-4a1e-83b4-e2cace82e951
-- title:
--   All-exponent spectral trace formula and reverse trace Young inequality
-- statement:
--   Let $H$ be a finite-dimensional complex Hilbert space, possibly of dimension zero. This part first extends the spectral trace formula to every real exponent $p$ for a positive semidefinite, invertible operator $X$:
--   $$
--   \operatorname{Tr}(X^p)=\sum_{i=1}^{\dim_{\mathbb C}H}\lambda_i(X)^p,
--   \qquad p\in\mathbb R.
--   $$
--   All eigenvalues are strictly positive by the preceding part, so negative powers in this formula are ordinary nonsingular spectral powers.
--
--   It then proves reverse trace Young inequality. Suppose $r<0$, $0<s<1$, and $1/r+1/s=1$. If $M$ is positive semidefinite and invertible and $N$ is positive semidefinite, then
--   $$
--   \frac{\operatorname{Tr}(M^r)}r+
--    \frac{\operatorname{Tr}(N^s)}s\le\operatorname{Tr}(MN).
--   $$
--   The powers use real continuous functional calculus and the trace is ordinary and unnormalized. $N$ may be singular, with zero eigenvalues contributing zero to $N^s$; invertibility is required only for $M$, whose exponent is negative. The formal statement compares complex traces in the complex order, and the displayed quantities are real under the stated positivity assumptions. No trace-one normalization, commutativity condition, or nonzero-dimension hypothesis is imposed. This part contains precisely these two extensions of the spectral and weighted reverse-Young infrastructure supplied by its predecessor.
-- source:
--   https://github.com/Hayata-Yamasaki-Group/lean-quantum/blob/bf1c4f6aaec84948f1a1c76c0728432813404a0f/Quantum/QuantumEntropy/YoungInequality.lean#L606-L749

import Mathlib.Analysis.CStarAlgebra.CompletelyPositiveMap
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Order
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.InnerProductSpace.TensorProduct
import Mathlib.Analysis.InnerProductSpace.Trace
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.MeanInequalities
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Trace
import Mathlib.Topology.Algebra.Module.LinearMapPiProd
import Definitions.Def_CRCD_Quantum_QuantumEntropy_YoungInequality_part_1
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumChannel_part_4
import Definitions.Def_CRCD_Quantum_QuantumMechanics_QuantumState









open QuantumState
open scoped ComplexOrder
open scoped MatrixOrder
open scoped Matrix.Norms.L2Operator

universe u

































section ReverseYoung















set_option backward.isDefEq.respectTransparency false in
/-- Trace of rpow for pd operators as sum of eigenvalue powers (all exponents). -/
lemma trace_rpow_eq_sum_eigenvalues_pd {ℋ : Type u} [Qudit ℋ]
    (X : L ℋ) (hX : X.IsPositive) (hX_unit : IsUnit X) (p : ℝ) :
    Tr (CFC.rpow X p)
      = ((((∑ i : Fin (Module.finrank ℂ ℋ),
              (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) : ℝ)) : ℂ) := by
  by_cases hp : 0 ≤ p
  · exact trace_rpow_eq_sum_eigenvalues X hX p hp
  · push_neg at hp
    let bx := hX.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
    let eVals : Fin (Module.finrank ℂ ℋ) → ℝ :=
      fun i => hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i
    let M : Matrix (Fin (Module.finrank ℂ ℋ)) (Fin (Module.finrank ℂ ℋ)) ℂ :=
      LinearMap.toMatrixOrthonormal bx X
    have hXnonneg : 0 ≤ X := (LinearMap.nonneg_iff_isPositive X).2 hX
    have hMnonneg : 0 ≤ M := by
      simpa [M] using map_nonneg (LinearMap.toMatrixOrthonormal bx) hXnonneg
    have hMpsd : M.PosSemidef := (Matrix.nonneg_iff_posSemidef).1 hMnonneg
    have hMherm : M.IsHermitian := hMpsd.1
    have hrootsM :
        M.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hMherm.eigenvalues) Finset.univ.val :=
      hMherm.roots_charpoly_eq_eigenvalues
    have hrootsDiag :
        M.charpoly.roots = Multiset.map (RCLike.ofReal ∘ eVals) Finset.univ.val := by
      have hdiagM : M = Matrix.diagonal (fun i =>
        (((hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) : ℝ) : ℂ)) := by
        simpa [M, eVals] using toMatrixOrthonormal_eq_diagonal_eigenvalues X hX
      rw [hdiagM, Matrix.charpoly_diagonal]
      have hroots :
          (Polynomial.roots
            (∏ i : Fin (Module.finrank ℂ ℋ),
              (Polynomial.X - Polynomial.C ((((eVals i) : ℝ) : ℂ))))
              ) = (Finset.univ.val.bind fun i : Fin (Module.finrank ℂ ℋ) =>
                  Polynomial.roots (Polynomial.X - Polynomial.C ((((eVals i) : ℝ) : ℂ)))) := by
        exact Polynomial.roots_prod
          (f := fun i : Fin (Module.finrank ℂ ℋ) =>
            (Polynomial.X - Polynomial.C ((((eVals i) : ℝ) : ℂ))))
          (s := Finset.univ)
          (Finset.prod_ne_zero_iff.mpr (by
            intro i hi
            exact Polynomial.X_sub_C_ne_zero _))
      rw [hroots]
      simp
    have hrealMulti :
        Multiset.map hMherm.eigenvalues Finset.univ.val = Multiset.map eVals Finset.univ.val := by
      have hrootsEq :
          Multiset.map ((fun x : ℝ => (x : ℂ)) ∘ hMherm.eigenvalues) Finset.univ.val
            = Multiset.map ((fun x : ℝ => (x : ℂ)) ∘ eVals) Finset.univ.val := by
        exact hrootsM.symm.trans hrootsDiag
      have hre := congrArg (Multiset.map Complex.re) hrootsEq
      simpa [Function.comp, eVals] using hre
    have hsumPow :
        (∑ i : Fin (Module.finrank ℂ ℋ), (hMherm.eigenvalues i) ^ p)
          = ∑ i : Fin (Module.finrank ℂ ℋ), (eVals i) ^ p :=
      sum_rpow_eq_of_multiset_map_eq (hMherm.eigenvalues) eVals p hrealMulti
    have hsumPowC :
        (((∑ i : Fin (Module.finrank ℂ ℋ), (hMherm.eigenvalues i) ^ p) : ℝ) : ℂ)
          = (((∑ i : Fin (Module.finrank ℂ ℋ), (eVals i) ^ p) : ℝ) : ℂ) := by
      exact congrArg (fun r : ℝ => (r : ℂ)) hsumPow
    calc
      Tr (CFC.rpow X p) = Matrix.trace (LinearMap.toMatrixOrthonormal bx (CFC.rpow X p)) :=
        tr_eq_matrix_trace_orthonormal bx (CFC.rpow X p)
      _ = Matrix.trace (CFC.rpow M p) := by
        exact (by
          have hmap := toMatrixOrthonormal_rpow_pd bx X hX hX_unit p
          simpa [M] using congrArg Matrix.trace hmap)
      _ = ∑ i : Fin (Module.finrank ℂ ℋ), (((hMherm.eigenvalues i) ^ p : ℝ) : ℂ) := by
        exact matrix_trace_rpow_eq_sum_eigenvalues M hMherm hMnonneg p
      _ = (((∑ i : Fin (Module.finrank ℂ ℋ), (hMherm.eigenvalues i) ^ p) : ℝ) : ℂ) := by
        simp
      _ = (((∑ i : Fin (Module.finrank ℂ ℋ), (eVals i) ^ p) : ℝ) : ℂ) := hsumPowC
      _ = ((((∑ i : Fin (Module.finrank ℂ ℋ),
                (hX.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ p) : ℝ)) : ℂ) := by
        simp [eVals]

set_option backward.isDefEq.respectTransparency false in
/-- Reverse trace Young inequality: for r < 0, s ∈ (0, 1), 1/r + 1/s = 1,
    M positive definite, N positive semidefinite:
    Tr(M^r)/r + Tr(N^s)/s ≤ Tr(M ∘ₗ N). -/
theorem trace_reverse_young_inequality {ℋ : Type u} [Qudit ℋ] {r s : ℝ}
    (hr : r < 0) (hs0 : 0 < s) (hs1 : s < 1) (hrs : 1 / r + 1 / s = 1)
    (M N : L ℋ) (hM : M.IsPositive) (hM_unit : IsUnit M) (hN : N.IsPositive) :
    Tr (CFC.rpow M r) / r + Tr (CFC.rpow N s) / s ≤ Tr (M ∘ₗ N) := by
  let bM := hM.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  let bN := hN.isSymmetric.eigenvectorBasis (n := Module.finrank ℂ ℋ) rfl
  have hdouble := trace_comp_eq_double_sum_eigen_overlap M N hM hN
  have hMpos :
      ∀ i : Fin (Module.finrank ℂ ℋ),
        0 < hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i :=
    pos_eigenvalues_of_isPositive_isUnit M hM hM_unit
  have hNnonneg :
      ∀ j : Fin (Module.finrank ℂ ℋ),
        0 ≤ hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j := by
    intro j
    exact hN.nonneg_eigenvalues (hn := rfl) j
  have hRevYoung :=
    weighted_reverse_young_overlap hr hs0 hs1 hrs bM bN
      (fun i => hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
      (fun j => hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
      hMpos hNnonneg
  have hbound_double_real :
      ((∑ i : Fin (Module.finrank ℂ ℋ),
            (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ r) / r : ℝ)
          + ((∑ j : Fin (Module.finrank ℂ ℋ),
            (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ s) / s : ℝ)
        ≤ (∑ j : Fin (Module.finrank ℂ ℋ),
          (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                  * Complex.normSq (inner ℂ (bM i) (bN j)))) := by
    calc
      ((∑ i : Fin (Module.finrank ℂ ℋ),
            (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i) ^ r) / r : ℝ)
          + ((∑ j : Fin (Module.finrank ℂ ℋ),
            (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j) ^ s) / s : ℝ)
        ≤ ∑ i : Fin (Module.finrank ℂ ℋ), ∑ j : Fin (Module.finrank ℂ ℋ),
            (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
              * (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
              * ‖inner ℂ (bM i) (bN j)‖ ^ 2 := hRevYoung
      _ = ∑ j : Fin (Module.finrank ℂ ℋ), ∑ i : Fin (Module.finrank ℂ ℋ),
            (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
              * (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
              * ‖inner ℂ (bM i) (bN j)‖ ^ 2 := Finset.sum_comm
      _ = ∑ j : Fin (Module.finrank ℂ ℋ),
          (hN.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl j)
            * (∑ i : Fin (Module.finrank ℂ ℋ),
                (hM.isSymmetric.eigenvalues (n := Module.finrank ℂ ℋ) rfl i)
                  * Complex.normSq (inner ℂ (bM i) (bN j))) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl ?_
        intro i _
        simp [Complex.normSq_eq_norm_sq, mul_assoc, mul_left_comm]
  have hbound_double_complex :
      Tr (CFC.rpow M r) / r + Tr (CFC.rpow N s) / s
        ≤ Tr (M ∘ₗ N) := by
    rw [hdouble]
    have htraceM := trace_rpow_eq_sum_eigenvalues_pd M hM hM_unit r
    have hs_nonneg : 0 ≤ s := hs0.le
    have htraceN := trace_rpow_eq_sum_eigenvalues N hN s hs_nonneg
    rw [htraceM, htraceN]
    exact_mod_cast hbound_double_real
  exact hbound_double_complex
end ReverseYoung


