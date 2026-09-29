-- Prove2me | solution 2 for ConvexOptimization.lmi_strict_alternative
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-16T06:14:09.492661+00:00
-- url     : https://prove2.me/submissions/75288193-3fcb-41cc-a831-0e0690a227d7

import Mathlib
import Theorems.Thm_ConvexOptimization_psd_cone_self_dual
set_option maxHeartbeats 1200000

open scoped RealInnerProductSpace ENNReal
open scoped Pointwise
open Set
open Matrix

namespace LMIAux

noncomputable section

noncomputable instance matrixNormedAddCommGroup (n : ℕ) :
    NormedAddCommGroup (Matrix (Fin n) (Fin n) ℝ) := Pi.normedAddCommGroup
noncomputable instance matrixNormedSpace (n : ℕ) :
    NormedSpace ℝ (Matrix (Fin n) (Fin n) ℝ) := Pi.normedSpace
noncomputable instance matrixNormSMulClass (n : ℕ) :
    NormSMulClass ℝ (Matrix (Fin n) (Fin n) ℝ) := NormedSpace.toNormSMulClass

variable (n : ℕ)

def symmMatrixSubmodule : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | A.IsSymm}
  zero_mem' := Matrix.isSymm_zero
  add_mem' hA hB := hA.add hB
  smul_mem' r A hA := by simpa [Matrix.IsSymm] using congrArg (r • ·) hA

abbrev SymmMat := symmMatrixSubmodule n

noncomputable instance symmMatNormSMulClass (n : ℕ) :
    NormSMulClass ℝ (SymmMat n) where
  norm_smul r A := by
    change ‖r • (A : Matrix (Fin n) (Fin n) ℝ)‖ =
      ‖r‖ * ‖(A : Matrix (Fin n) (Fin n) ℝ)‖
    exact norm_smul r (A : Matrix (Fin n) (Fin n) ℝ)

noncomputable instance symmMatFiniteDimensional (n : ℕ) :
    FiniteDimensional ℝ (SymmMat n) :=
  FiniteDimensional.finiteDimensional_submodule (symmMatrixSubmodule n)

variable {n}

lemma sum_matrix_apply {k : Type*} [Fintype k] (f : k → Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : (∑ x, f x) i j = ∑ x, f x i j := by
  classical
  have hs : ∀ s : Finset k, (∑ x ∈ s, f x) i j = ∑ x ∈ s, f x i j := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert x s hx ih => simp [hx, ih, Matrix.add_apply]
  simpa using hs Finset.univ

def psdCone : Set (SymmMat n) := {A | A.1.PosSemidef}

lemma zero_mem_psdCone : (0 : SymmMat n) ∈ psdCone := Matrix.PosSemidef.zero

lemma convex_psdCone : Convex ℝ (psdCone : Set (SymmMat n)) := by
  intro A hA B hB a b ha hb hab
  change (a • (A : Matrix (Fin n) (Fin n) ℝ) + b • B).PosSemidef
  exact (hA.smul ha).add (hB.smul hb)

lemma rankOne_psd (x : Fin n → ℝ) : (Matrix.vecMulVec x x).PosSemidef := by
  simpa using posSemidef_vecMulVec_self_star x

def symBasis (i j : Fin n) : SymmMat n :=
  ⟨(2 : ℝ)⁻¹ • (Matrix.vecMulVec (Pi.single i 1) (Pi.single j 1) +
      Matrix.vecMulVec (Pi.single j 1) (Pi.single i 1)), by
    ext p q
    simp [Matrix.transpose_apply, Matrix.vecMulVec_apply, and_comm, eq_comm, add_comm]
    ring⟩

lemma symBasis_comm (i j : Fin n) : symBasis i j = symBasis j i := by
  apply Subtype.ext
  simp [symBasis, add_comm]

lemma symm_expansion (A : SymmMat n) :
    A = ∑ i, ∑ j, A.1 i j • symBasis i j := by
  classical
  apply Subtype.ext
  change A.1 = (↑(∑ i, ∑ j, A.1 i j • symBasis i j) :
    Matrix (Fin n) (Fin n) ℝ)
  rw [Submodule.coe_sum]
  simp_rw [Submodule.coe_sum, Submodule.coe_smul]
  ext p q
  simp only [sum_matrix_apply]
  simp only [symBasis, Matrix.smul_apply, Matrix.add_apply, Matrix.vecMulVec_apply,
    smul_eq_mul]
  let e : Fin n → Fin n → ℝ := fun i j =>
    A.1 i j * ((Pi.single i (1 : ℝ) : Fin n → ℝ) p *
      (Pi.single j (1 : ℝ) : Fin n → ℝ) q) * (1 / 2)
  let et : Fin n → Fin n → ℝ := fun i j =>
    A.1 i j * ((Pi.single j (1 : ℝ) : Fin n → ℝ) p *
      (Pi.single i (1 : ℝ) : Fin n → ℝ) q) * (1 / 2)
  have h1 : (∑ i, ∑ j, e i j) = A.1 p q / 2 := by
    rw [Fintype.sum_eq_single p (fun i hip => by simp [e, Pi.single_apply, hip.symm])]
    rw [Fintype.sum_eq_single q (fun j hjq => by simp [e, Pi.single_apply, hjq.symm])]
    dsimp [e]
    simp
    ring
  have h2 : (∑ i, ∑ j, et i j) = A.1 q p / 2 := by
    rw [Fintype.sum_eq_single q (fun i hiq => by simp [et, Pi.single_apply, hiq.symm])]
    rw [Fintype.sum_eq_single p (fun j hjp => by simp [et, Pi.single_apply, hjp.symm])]
    dsimp [et]
    simp
    ring
  have hsplit : (∑ i, ∑ j, (e i j + et i j)) =
      (∑ i, ∑ j, e i j) + ∑ i, ∑ j, et i j := by
    simp only [Finset.sum_add_distrib]
  have hterm : ∀ i j, A.1 i j * (2⁻¹ *
      ((Pi.single i (1 : ℝ) : Fin n → ℝ) p * (Pi.single j (1 : ℝ) : Fin n → ℝ) q +
       (Pi.single j (1 : ℝ) : Fin n → ℝ) p * (Pi.single i (1 : ℝ) : Fin n → ℝ) q)) =
      e i j + et i j := by
    intro i j
    dsimp [e, et]
    ring
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hterm i j]
  rw [hsplit, h1, h2]
  have hs := congrFun (congrFun A.2 q) p
  simp [Matrix.transpose_apply] at hs
  rw [hs]
  ring

lemma interior_psdCone_nonempty :
    (interior (psdCone : Set (SymmMat n))).Nonempty := by
  classical
  let I : SymmMat n := ⟨1, Matrix.isSymm_one⟩
  let δ : ℝ := 1 / (2 * ((n : ℝ) + 1))
  let U : Set (SymmMat n) := {B | ∀ i j, |B.1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j| < δ}
  have hδ : 0 < δ := by
    dsimp [δ]
    positivity
  have hUopen : IsOpen U := by
    have heq : U = ⋂ i, ⋂ j, {B : SymmMat n |
        |B.1 i j - (1 : Matrix (Fin n) (Fin n) ℝ) i j| < δ} := by
      ext B
      simp [U]
    rw [heq]
    apply isOpen_iInter_of_finite
    intro i
    apply isOpen_iInter_of_finite
    intro j
    have hc : Continuous (fun B : SymmMat n => B.1 i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp continuous_subtype_val)
    exact isOpen_lt (hc.sub continuous_const).abs continuous_const
  have hIU : I ∈ U := by
    intro i j
    simp [I, hδ]
  have hUK : U ⊆ psdCone := by
    intro B hB
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
      exact B.2
    · intro x
      let E : Matrix (Fin n) (Fin n) ℝ := B.1 - 1
      let S : ℝ := ∑ i, x i ^ 2
      have hcoord : ∀ i j, |E i j| ≤ δ := by
        intro i j
        exact (hB i j).le
      have hterm : ∀ i j,
          -(δ / 2) * (x i ^ 2 + x j ^ 2) ≤ x i * E i j * x j := by
        intro i j
        have habsE : 0 ≤ |E i j| := abs_nonneg _
        have hxy : 0 ≤ |x i| * |x j| := mul_nonneg (abs_nonneg _) (abs_nonneg _)
        have hm := mul_le_mul_of_nonneg_right (hcoord i j) hxy
        have hamgm : 2 * (|x i| * |x j|) ≤ x i ^ 2 + x j ^ 2 := by
          nlinarith [sq_nonneg (|x i| - |x j|), sq_abs (x i), sq_abs (x j)]
        have habsterm : |x i * E i j * x j| ≤
            (δ / 2) * (x i ^ 2 + x j ^ 2) := by
          rw [abs_mul, abs_mul]
          nlinarith
        calc
          -(δ / 2) * (x i ^ 2 + x j ^ 2) =
              -(δ / 2 * (x i ^ 2 + x j ^ 2)) := by ring
          _ ≤ -|x i * E i j * x j| := neg_le_neg habsterm
          _ ≤ _ := neg_abs_le _
      have herr : -(δ * (n : ℝ)) * S ≤ ∑ i, ∑ j, x i * E i j * x j := by
        have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
          Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hterm i j
        have hcalc : (∑ i, ∑ j, -(δ / 2) * (x i ^ 2 + x j ^ 2)) =
            -(δ * (n : ℝ)) * S := by
          have hinner : ∀ i, (∑ j, (x i ^ 2 + x j ^ 2)) = (n : ℝ) * x i ^ 2 + S := by
            intro i
            rw [Finset.sum_add_distrib]
            simp [S, Finset.card_univ, Fintype.card_fin]
          rw [show (∑ i, ∑ j, -(δ / 2) * (x i ^ 2 + x j ^ 2)) =
              ∑ i, -(δ / 2) * ((n : ℝ) * x i ^ 2 + S) by
            apply Finset.sum_congr rfl
            intro i hi
            rw [← Finset.mul_sum, hinner i]]
          rw [show (∑ i, -(δ / 2) * ((n : ℝ) * x i ^ 2 + S)) =
              ∑ i, (-(δ / 2) * (n : ℝ) * x i ^ 2 + -(δ / 2) * S) by
            apply Finset.sum_congr rfl
            intro i hi
            ring]
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin]
          dsimp [S]
          rw [← Finset.mul_sum]
          ring
        rw [hcalc] at hs
        exact hs
      have hδn : δ * (n : ℝ) ≤ 1 := by
        dsimp [δ]
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        have hd : 0 < 2 * ((n : ℝ) + 1) := by positivity
        rw [show 1 / (2 * ((n : ℝ) + 1)) * (n : ℝ) =
          (n : ℝ) / (2 * ((n : ℝ) + 1)) by ring]
        exact (div_le_one hd).2 (by nlinarith)
      have hS : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hquadE : x ⬝ᵥ E.mulVec x = ∑ i, ∑ j, x i * E i j * x j := by
        simp only [dotProduct, Matrix.mulVec]
        apply Finset.sum_congr rfl
        intro i hi
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      have hquadI : x ⬝ᵥ (1 : Matrix (Fin n) (Fin n) ℝ).mulVec x = S := by
        simp only [dotProduct, Matrix.one_mulVec]
        dsimp [S]
        apply Finset.sum_congr rfl
        intro i hi
        ring
      have hBE : B.1 = (1 : Matrix (Fin n) (Fin n) ℝ) + E := by
        dsimp [E]
        abel
      rw [hBE, Matrix.add_mulVec, dotProduct_add]
      change 0 ≤ x ⬝ᵥ (1 : Matrix (Fin n) (Fin n) ℝ).mulVec x + x ⬝ᵥ E.mulVec x
      rw [hquadI, hquadE]
      nlinarith
  refine ⟨I, interior_maximal hUK hUopen hIU⟩

end
end LMIAux

namespace LMIAux
noncomputable section
variable {n : ℕ}

lemma isClosed_psdCone : IsClosed (psdCone : Set (SymmMat n)) := by
  have heq : (psdCone : Set (SymmMat n)) =
      ⋂ x : Fin n → ℝ, {A | 0 ≤ x ⬝ᵥ (A.1.mulVec x)} := by
    ext A
    simp only [psdCone, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro h x
      simpa using h.dotProduct_mulVec_nonneg x
    · intro h
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      · rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
        exact A.2
      · simpa using h
  rw [heq]
  apply isClosed_iInter
  intro x
  exact isClosed_le continuous_const (by fun_prop)

lemma interior_psdCone_subset : interior (psdCone : Set (SymmMat n)) ⊆ psdCone :=
  interior_subset

lemma quad_rankOne_self (x : Fin n → ℝ) :
    x ⬝ᵥ (Matrix.vecMulVec x x).mulVec x = (x ⬝ᵥ x) ^ 2 := by
  simp only [dotProduct, Matrix.mulVec, Matrix.vecMulVec_apply]
  calc
    (∑ i, x i * ∑ j, x i * x j * x j) =
        ∑ i, (x i * x i) * ∑ j, x j * x j := by
          apply Finset.sum_congr rfl
          intro i hi
          calc
            x i * ∑ j, x i * x j * x j =
                x i * (x i * ∑ j, x j * x j) := by
                  congr 1
                  calc
                    (∑ j, x i * x j * x j) = ∑ j, x i * (x j * x j) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
                    _ = _ := by rw [Finset.mul_sum]
            _ = _ := by ring
    _ = (∑ i, x i * x i) * ∑ j, x j * x j := by rw [Finset.sum_mul]
    _ = _ := by ring

lemma interior_psdCone_posDef {A : SymmMat n}
    (hA : A ∈ interior (psdCone : Set (SymmMat n))) : A.1.PosDef := by
  apply Matrix.PosDef.of_dotProduct_mulVec_pos
  · rw [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial]
    exact A.2
  · intro x hx
    have hpsdm : A ∈ psdCone := interior_subset hA
    have hpsd : A.1.PosSemidef := hpsdm
    have hnonneg := hpsd.dotProduct_mulVec_nonneg x
    by_contra hnpos
    have hzero : x ⬝ᵥ A.1.mulVec x = 0 := le_antisymm (le_of_not_gt hnpos) hnonneg
    let Rm : Matrix (Fin n) (Fin n) ℝ := Matrix.vecMulVec x x
    have hRsymm : Rm.IsSymm := by
      ext i j
      simp [Rm, Matrix.transpose_apply, Matrix.vecMulVec_apply, mul_comm]
    let R : SymmMat n := ⟨Rm, hRsymm⟩
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior A hA
    let t : ℝ := ε / (2 * (‖R‖ + 1))
    have ht : 0 < t := div_pos hε (mul_pos (by norm_num) (by positivity))
    have hdist : dist (A - t • R) A < ε := by
      rw [dist_eq_norm]
      have heq : A - t • R - A = -(t • R) := by abel
      calc
        ‖A - t • R - A‖ = ‖-(t • R)‖ := congrArg norm heq
        _ = ‖t • R‖ := norm_neg _
        _ = t * ‖R‖ := by rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
        _ < ε := by
          dsimp [t]
          have hr : 0 ≤ ‖R‖ := norm_nonneg _
          have hnorm : ‖(R : Matrix (Fin n) (Fin n) ℝ)‖ = ‖R‖ := rfl
          have hd : 0 < 2 * (‖R‖ + 1) := by positivity
          rw [div_mul_eq_mul_div]
          apply (div_lt_iff₀ hd).2
          nlinarith [hnorm]
    have hB : (A - t • R) ∈ psdCone := interior_subset (hball hdist)
    have hq := hB.dotProduct_mulVec_nonneg x
    change 0 ≤ x ⬝ᵥ (A.1 - t • Rm).mulVec x at hq
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
      hzero, quad_rankOne_self] at hq
    have hxex : ∃ i, x i ≠ 0 := by
      by_contra hn
      push Not at hn
      exact hx (funext hn)
    have hxx : 0 < x ⬝ᵥ x := by
      simp only [dotProduct]
      apply Finset.sum_pos'
      · intro i hi; exact mul_self_nonneg _
      · obtain ⟨i, hi⟩ := hxex
        exact ⟨i, Finset.mem_univ _, mul_self_pos.mpr hi⟩
    change 0 ≤ 0 - t * (x ⬝ᵥ x) ^ 2 at hq
    nlinarith [sq_pos_of_pos hxx]

end
end LMIAux

namespace LMIAux
noncomputable section
variable {n : ℕ}

def representingMatrix (f : StrongDual ℝ (SymmMat n)) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => f (symBasis i j)

lemma representingMatrix_isSymm (f : StrongDual ℝ (SymmMat n)) :
    (representingMatrix f).IsSymm := by
  ext i j
  change f (symBasis j i) = f (symBasis i j)
  rw [symBasis_comm]

lemma functional_eq_trace (f : StrongDual ℝ (SymmMat n)) (A : SymmMat n) :
    f A = (A.1 * representingMatrix f).trace := by
  calc
    f A = ∑ i, ∑ j, A.1 i j * f (symBasis i j) := by
      conv_lhs => rw [symm_expansion A]
      simp
    _ = ∑ i, ∑ j, A.1 i j * representingMatrix f j i := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [show representingMatrix f j i = f (symBasis i j) by
        dsimp [representingMatrix]
        rw [symBasis_comm]]
    _ = _ := by simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]

lemma smul_mem_psdCone {A : SymmMat n} (hA : A ∈ psdCone) {t : ℝ} (ht : 0 ≤ t) :
    t • A ∈ psdCone := hA.smul ht

lemma interior_add_psd {A B : SymmMat n}
    (hA : A ∈ interior (psdCone : Set (SymmMat n))) (hB : B ∈ psdCone) :
    A + B ∈ interior (psdCone : Set (SymmMat n)) := by
  have hsub : (fun y => y + B) '' interior (psdCone : Set (SymmMat n)) ⊆ psdCone := by
    rintro _ ⟨y, hy, rfl⟩
    exact (interior_subset hy).add hB
  have hopen : IsOpen ((fun y => y + B) '' interior (psdCone : Set (SymmMat n))) := by
    simpa using (Homeomorph.addRight B).isOpenMap _ isOpen_interior
  exact interior_maximal hsub hopen ⟨A, hA, rfl⟩

lemma smul_mem_interior_psd {A : SymmMat n}
    (hA : A ∈ interior (psdCone : Set (SymmMat n))) {r : ℝ} (hr : 0 < r) :
    r • A ∈ interior (psdCone : Set (SymmMat n)) := by
  have heq : r • (psdCone : Set (SymmMat n)) = psdCone := by
    ext Z
    constructor
    · rintro ⟨W, hW, rfl⟩
      exact hW.smul hr.le
    · intro hZ
      refine ⟨r⁻¹ • Z, hZ.smul (inv_nonneg.mpr hr.le), ?_⟩
      change r • (r⁻¹ • Z) = Z
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  rw [← heq, interior_smul₀ hr.ne']
  exact ⟨A, hA, rfl⟩

lemma trace_pos_of_posDef_psd {P Z : Matrix (Fin n) (Fin n) ℝ}
    (hP : P.PosDef) (hZ : Z.PosSemidef) (hZ0 : Z ≠ 0) : 0 < (P * Z).trace := by
  classical
  let v : Fin n → Fin n → ℝ := fun i =>
    Real.sqrt (hZ.isHermitian.eigenvalues i) •
      Matrix.col (hZ.isHermitian.eigenvectorUnitary : Matrix (Fin n) (Fin n) ℝ) i
  have hdecomp : Z = ∑ i, Matrix.vecMulVec (v i) (v i) := by
    calc
      Z = Unitary.conjStarAlgAut ℝ (Matrix (Fin n) (Fin n) ℝ)
          hZ.isHermitian.eigenvectorUnitary
          (Matrix.diagonal (RCLike.ofReal ∘ hZ.isHermitian.eigenvalues)) :=
        hZ.isHermitian.spectral_theorem
      _ = ∑ i, Matrix.vecMulVec (v i) (v i) := by
        ext i j
        simp [Unitary.conjStarAlgAut_apply, Matrix.mul_apply, Matrix.diagonal, v,
          Matrix.vecMulVec_apply]
        rw [sum_matrix_apply]
        apply Finset.sum_congr rfl
        intro k hk
        simp [v, Matrix.smul_apply, Matrix.vecMulVec_apply]
        have hs := Real.sq_sqrt (hZ.eigenvalues_nonneg k)
        calc
          _ = hZ.isHermitian.eigenvalues k *
              ((hZ.isHermitian.eigenvectorBasis k).ofLp i *
                (hZ.isHermitian.eigenvectorBasis k).ofLp j) := by ring
          _ = Real.sqrt (hZ.isHermitian.eigenvalues k) ^ 2 *
              ((hZ.isHermitian.eigenvectorBasis k).ofLp i *
                (hZ.isHermitian.eigenvectorBasis k).ofLp j) := by rw [hs]
          _ = _ := by ring
  have hvne : ∃ i, v i ≠ 0 := by
    by_contra hn
    push_neg at hn
    have : (∑ i, Matrix.vecMulVec (v i) (v i)) = 0 := by simp [hn]
    exact hZ0 (hdecomp.trans this)
  rw [hdecomp, Matrix.mul_sum]
  have htrace : (∑ i, P * Matrix.vecMulVec (v i) (v i)).trace =
      ∑ i, v i ⬝ᵥ P.mulVec (v i) := by
    calc
      _ = ∑ i, (P * Matrix.vecMulVec (v i) (v i)).trace := by
        simpa using map_sum (Matrix.traceLinearMap (Fin n) ℝ ℝ)
          (fun i => P * Matrix.vecMulVec (v i) (v i)) Finset.univ
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [dotProduct, Matrix.mulVec, Matrix.trace, Matrix.diag, Matrix.mul_apply,
          Matrix.vecMulVec_apply]
        simp_rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j hj
        apply Finset.sum_congr rfl
        intro k hk
        ring
  rw [htrace]
  apply Finset.sum_pos'
  · intro i hi
    exact (hP.posSemidef.dotProduct_mulVec_nonneg _)
  · obtain ⟨i, hi⟩ := hvne
    exact ⟨i, Finset.mem_univ _, hP.dotProduct_mulVec_pos hi⟩

lemma posDef_mem_interior {A : SymmMat n} (hA : A.1.PosDef) :
    A ∈ interior (psdCone : Set (SymmMat n)) := by
  by_contra hnot
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point
    (convex_psdCone (n := n)).interior isOpen_interior hnot
  obtain ⟨Y, hY⟩ := interior_psdCone_nonempty (n := n)
  have hfY : f Y ≤ 0 := by
    by_contra hp
    have hp' : 0 < f Y := lt_of_not_ge hp
    have hh := hf (max 1 ((f A + 1) / f Y) • Y)
      (smul_mem_interior_psd hY (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    simp only [map_smul, smul_eq_mul] at hh
    have hm : (f A + 1) / f Y ≤ max 1 ((f A + 1) / f Y) := le_max_right _ _
    have := mul_le_mul_of_nonneg_right hm hp'.le
    field_simp at this
    linarith
  have hfA : 0 ≤ f A := by
    by_contra hn
    have hfa : f A < 0 := lt_of_not_ge hn
    let r : ℝ := (-f A) / (2 * (|f Y| + 1))
    have hr : 0 < r := div_pos (neg_pos.mpr hfa) (by positivity)
    have hh := hf (r • Y) (smul_mem_interior_psd hY hr)
    simp only [map_smul, smul_eq_mul] at hh
    have habs := le_abs_self (f Y)
    have habs' := neg_le_abs (f Y)
    have hden : 0 < 2 * (|f Y| + 1) := by positivity
    dsimp [r] at hh
    field_simp [ne_of_gt hden] at hh
    nlinarith [abs_nonneg (f Y)]
  have hfK : ∀ B ∈ psdCone, f B ≤ 0 := by
    intro B hB
    by_contra hp
    have hp' : 0 < f B := lt_of_not_ge hp
    have hYB : ∀ r : ℝ, 0 < r → Y + r • B ∈ interior (psdCone : Set (SymmMat n)) := by
      intro r hr
      exact interior_add_psd hY (hB.smul hr.le)
    have hh := hf (Y + max 1 ((f A - f Y + 1) / f B) • B)
      (hYB _ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))
    simp only [map_add, map_smul, smul_eq_mul] at hh
    have hm : (f A - f Y + 1) / f B ≤
        max 1 ((f A - f Y + 1) / f B) := le_max_right _ _
    have := mul_le_mul_of_nonneg_right hm hp'.le
    field_simp at this
    linarith
  let Z : Matrix (Fin n) (Fin n) ℝ := -representingMatrix f
  have hZsymm : Z.IsSymm := (representingMatrix_isSymm f).neg
  have hZpsd : Z.PosSemidef := by
    apply (ConvexOptimization.psd_cone_self_dual Z hZsymm).mp
    intro B hB
    let Bs : SymmMat n := ⟨B, by
      exact hB.isHermitian.eq⟩
    have := hfK Bs hB
    rw [functional_eq_trace] at this
    dsimp [Z]
    calc
      0 ≤ -((B * representingMatrix f).trace) := by linarith
      _ = ((-representingMatrix f) * B).trace := by
        calc
          -((B * representingMatrix f).trace) =
              -((representingMatrix f * B).trace) :=
            congrArg Neg.neg (Matrix.trace_mul_comm B (representingMatrix f))
          _ = (-(representingMatrix f * B)).trace := by
            exact (map_neg (Matrix.traceLinearMap (Fin n) ℝ ℝ)
              (representingMatrix f * B)).symm
          _ = ((-representingMatrix f) * B).trace := by rw [Matrix.neg_mul]
  have hZ0 : Z ≠ 0 := by
    intro hz
    have hf0 : f = 0 := by
      apply ContinuousLinearMap.ext
      intro B
      change f B = 0
      rw [functional_eq_trace]
      have hr : representingMatrix f = 0 := by
        dsimp [Z] at hz
        exact neg_eq_zero.mp hz
      rw [hr, Matrix.mul_zero, Matrix.trace_zero]
    subst f
    simpa using hf Y hY
  have htrace := trace_pos_of_posDef_psd hA hZpsd hZ0
  have hfa : f A = -((A.1 * Z).trace) := by
    rw [functional_eq_trace]
    dsimp [Z]
    simp
  linarith

lemma interior_psdCone_iff_posDef (A : SymmMat n) :
    A ∈ interior (psdCone : Set (SymmMat n)) ↔ A.1.PosDef :=
  ⟨interior_psdCone_posDef, posDef_mem_interior⟩

end
end LMIAux

namespace LMIAux
noncomputable section
variable {n nn : ℕ}

lemma trace_sum_mul (F : Fin n → Matrix (Fin nn) (Fin nn) ℝ) (x : Fin n → ℝ)
    (Z : Matrix (Fin nn) (Fin nn) ℝ) :
    (((∑ i, x i • F i) * Z).trace) = ∑ i, x i * ((F i * Z).trace) := by
  rw [Matrix.sum_mul]
  calc
    (∑ i, (x i • F i) * Z).trace = ∑ i, (((x i • F i) * Z).trace) := by
      simpa using map_sum (Matrix.traceLinearMap (Fin nn) ℝ ℝ)
        (fun i => (x i • F i) * Z) Finset.univ
    _ = _ := by simp [Matrix.smul_mul, map_smul]

lemma isSymm_sum (M : Fin n → Matrix (Fin nn) (Fin nn) ℝ)
    (hM : ∀ i, (M i).IsSymm) : (∑ i, M i).IsSymm := by
  classical
  have hs : ∀ s : Finset (Fin n), (∑ i ∈ s, M i).IsSymm := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp [Matrix.isSymm_zero]
    | insert i s hi ih => simpa [hi] using (hM i).add ih
  simpa using hs Finset.univ

end
end LMIAux

open LMIAux

open ConvexOptimization in
theorem solution {n nn : ℕ}
    (F : Fin n → Matrix (Fin nn) (Fin nn) ℝ) (hF : ∀ i, (F i).IsSymm)
    (G : Matrix (Fin nn) (Fin nn) ℝ) (hG : G.IsSymm) :
    (∃ x : Fin n → ℝ, (-(G + ∑ i, x i • F i)).PosDef) ↔
      ¬∃ Z : Matrix (Fin nn) (Fin nn) ℝ, Z.PosSemidef ∧ Z ≠ 0 ∧
        (∀ i, ((F i) * Z).trace = 0) ∧ 0 ≤ (G * Z).trace := by
  classical
  cases isEmpty_or_nonempty (Fin nn) with
  | inl hempty =>
    letI : IsEmpty (Fin nn) := hempty
    constructor
    · intro hx
      rintro ⟨Z, hZ, hZ0, hZF, hZG⟩
      exact hZ0 (Subsingleton.elim _ _)
    · intro h
      refine ⟨0, ?_⟩
      constructor
      · ext i
        exact isEmptyElim i
      · intro x hx
        exact (hx (Subsingleton.elim _ _)).elim
  | inr hnonempty =>
    constructor
    · rintro ⟨x, hx⟩ ⟨Z, hZ, hZ0, hZF, hZG⟩
      have hp := trace_pos_of_posDef_psd hx hZ hZ0
      have he : ((-(G + ∑ i, x i • F i)) * Z).trace = -(G * Z).trace := by
        calc
          _ = -((G * Z).trace + (((∑ i, x i • F i) * Z).trace)) := by
            simp [Matrix.neg_mul, Matrix.add_mul]
          _ = _ := by rw [trace_sum_mul]; simp [hZF]
      rw [he] at hp
      linarith
    · intro hnoZ
      by_contra hnox
      push_neg at hnox
      let toS : (Fin n → ℝ) → SymmMat nn := fun x =>
        ⟨G + ∑ i, x i • F i, by
          apply hG.add
          exact isSymm_sum _ fun i => (hF i).smul _⟩
      let O : Set (SymmMat nn) := {A | -A ∈ interior (psdCone : Set (SymmMat nn))}
      let T : Set (SymmMat nn) := Set.range toS
      have hOopen : IsOpen O := by
        dsimp [O]
        exact isOpen_interior.preimage continuous_neg
      have hOconv : Convex ℝ O := by
        intro A hA B hB a b ha hb hab
        change -(a • A + b • B) ∈ interior (psdCone : Set (SymmMat nn))
        have hh := (convex_psdCone (n := nn)).interior hA hB ha hb hab
        change a • (-A) + b • (-B) ∈ interior (psdCone : Set (SymmMat nn)) at hh
        convert hh using 1 <;> module
      have hTconv : Convex ℝ T := by
        rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ a b ha hb hab
        refine ⟨a • x + b • y, ?_⟩
        apply Subtype.ext
        dsimp [toS]
        have hsum : (∑ i, (a * x i + b * y i) • F i) =
            a • (∑ i, x i • F i) + b • (∑ i, y i • F i) := by
          rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [add_smul, smul_smul, smul_smul]
        rw [hsum]
        calc
          G + (a • (∑ i, x i • F i) + b • (∑ i, y i • F i)) =
              (a + b) • G + (a • (∑ i, x i • F i) + b • (∑ i, y i • F i)) := by
                rw [hab, one_smul]
          _ = _ := by module
      have hdisj : Disjoint O T := by
        rw [Set.disjoint_left]
        intro A hAO hAT
        obtain ⟨x, rfl⟩ := hAT
        have hp : (-(G + ∑ i, x i • F i)).PosDef :=
          (interior_psdCone_iff_posDef _).mp hAO
        exact hnox x hp
      obtain ⟨f, u, hfO, hfT⟩ := geometric_hahn_banach_open hOconv hOopen hTconv hdisj
      obtain ⟨Y, hY⟩ := interior_psdCone_nonempty (n := nn)
      have hnegY : ∀ r : ℝ, 0 < r → -(r • Y) ∈ O := by
        intro r hr
        change -(-(r • Y)) ∈ interior (psdCone : Set (SymmMat nn))
        rw [neg_neg]
        exact posDef_mem_interior ((interior_psdCone_posDef hY).smul hr)
      have hu : 0 ≤ u := by
        by_contra hnu
        have hu0 : u < 0 := lt_of_not_ge hnu
        let r : ℝ := (-u) / (2 * (|f Y| + 1))
        have hr : 0 < r := div_pos (neg_pos.mpr hu0) (by positivity)
        have hh := hfO (-(r • Y)) (hnegY r hr)
        simp only [map_neg, map_smul, smul_eq_mul] at hh
        have habs := le_abs_self (f Y)
        have habs' := neg_le_abs (f Y)
        have hden : 0 < 2 * (|f Y| + 1) := by positivity
        dsimp [r] at hh
        field_simp [ne_of_gt hden] at hh
        nlinarith [abs_nonneg (f Y)]
      have hbound : ∀ x : Fin n → ℝ, u ≤ f (toS x) := fun x => hfT _ ⟨x, rfl⟩
      have hfFi : ∀ i, f (⟨F i, hF i⟩ : SymmMat nn) = 0 := by
        intro i
        let c := f (⟨F i, hF i⟩ : SymmMat nn)
        by_contra hc
        have hc0 : c ≠ 0 := hc
        let r : ℝ := (u - f (⟨G, hG⟩ : SymmMat nn) - 1) / c
        let x : Fin n → ℝ := fun j => if j = i then r else 0
        have hb := hbound x
        have hsum : (∑ j, x j • F j) = r • F i := by
          simp [x]
        have htoS : toS x =
            (⟨G, hG⟩ : SymmMat nn) + r • ⟨F i, hF i⟩ := by
          apply Subtype.ext
          dsimp [toS]
          rw [hsum]
        rw [htoS] at hb
        simp only [map_add, map_smul, smul_eq_mul] at hb
        dsimp [r, c] at hb hc0
        field_simp [hc0] at hb
        linarith
      have hfG : u ≤ f (⟨G, hG⟩ : SymmMat nn) := by
        simpa [toS] using hbound (0 : Fin n → ℝ)
      have hfPSD : ∀ B ∈ psdCone, 0 ≤ f B := by
        intro B hB
        by_contra hn
        have hfb : f B < 0 := lt_of_not_ge hn
        let r : ℝ := max 1 ((u + f Y + 1) / (-f B))
        have hr : 0 < r := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
        have hYi : Y + r • B ∈ interior (psdCone : Set (SymmMat nn)) :=
          interior_add_psd hY (hB.smul hr.le)
        have hh := hfO (-(Y + r • B)) (show -(Y + r • B) ∈ O by
          change -(-(Y + r • B)) ∈ interior (psdCone : Set (SymmMat nn))
          simpa using hYi)
        simp only [map_neg, map_add, map_smul, smul_eq_mul] at hh
        have hm : (u + f Y + 1) / (-f B) ≤ r := le_max_right _ _
        have hp : 0 < -f B := neg_pos.mpr hfb
        have hmul := mul_le_mul_of_nonneg_right hm hp.le
        rw [div_mul_cancel₀ _ hp.ne'] at hmul
        linarith
      let Z : Matrix (Fin nn) (Fin nn) ℝ := representingMatrix f
      have hZsymm : Z.IsSymm := representingMatrix_isSymm f
      have hZpsd : Z.PosSemidef := by
        apply (ConvexOptimization.psd_cone_self_dual Z hZsymm).mp
        intro B hB
        let Bs : SymmMat nn := ⟨B, by
          exact hB.isHermitian.eq⟩
        calc
          0 ≤ (Bs.1 * representingMatrix f).trace := by
            rw [← functional_eq_trace]
            exact hfPSD Bs hB
          _ = (Z * B).trace := by
            dsimp [Z]
            exact Matrix.trace_mul_comm B (representingMatrix f)
      have hZ0 : Z ≠ 0 := by
        intro hz
        have hfzero : f = 0 := by
          apply ContinuousLinearMap.ext
          intro B
          change f B = 0
          rw [functional_eq_trace]
          dsimp [Z] at hz
          rw [hz, Matrix.mul_zero, Matrix.trace_zero]
        subst f
        have ho : -Y ∈ O := by
          change -(-Y) ∈ interior (psdCone : Set (SymmMat nn))
          simpa using hY
        have := hfO (-Y) ho
        have hb0 := hfT (toS 0) ⟨0, rfl⟩
        change 0 < u at this
        change u ≤ 0 at hb0
        linarith
      exfalso
      apply hnoZ
      refine ⟨Z, hZpsd, hZ0, ?_, ?_⟩
      · intro i
        rw [← functional_eq_trace f (⟨F i, hF i⟩ : SymmMat nn)]
        change f (⟨F i, hF i⟩ : SymmMat nn) = 0
        exact hfFi i
      · rw [← functional_eq_trace f (⟨G, hG⟩ : SymmMat nn)]
        exact le_trans hu hfG
