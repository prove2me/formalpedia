-- Prove2me | solution 1 for first_neumann_certificate_term_as_negative_normal_projection_of_linear_correction
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-22T05:40:21.954384+00:00
-- url     : https://prove2.me/submissions/f351e5b4-e80d-4f4f-bf47-c154dd28bc19

import Definitions.Def_matrix_completion_neumann
import Definitions.Def_tangent_projection_algebra
import Mathlib.Analysis.InnerProductSpace.PiL2

open scoped Classical BigOperators

namespace MatrixCompletion

variable {n1 n2 r : Nat} {M : RealMatrix n1 n2}

/-! PT master expansion (toolkit). -/
lemma PT_X_entry' (S : SVD M r) (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    (tangentProjection S X) i j
      = (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * X a j)
        + (∑ b : Fin n2, X i b * (∑ l : Fin r, S.v l b * S.v l j))
        - (∑ a : Fin n1, ∑ b : Fin n2,
            (∑ k : Fin r, S.u k i * S.u k a) * X a b * (∑ l : Fin r, S.v l b * S.v l j)) := by
  unfold tangentProjection leftSingularProjection rightSingularProjection
    twoSidedSingularProjection
  simp only [Matrix.add_apply, Matrix.sub_apply]

lemma PT_coord_entry' (S : SVD M r) (w1 : Fin n1) (w2 : Fin n2) (i : Fin n1) (j : Fin n2) :
    (tangentProjection S (coordinateMatrix w1 w2)) i j
      = (if j = w2 then (∑ k : Fin r, S.u k i * S.u k w1) else 0)
        + (if i = w1 then (∑ l : Fin r, S.v l w2 * S.v l j) else 0)
        - (∑ k : Fin r, S.u k i * S.u k w1) * (∑ l : Fin r, S.v l w2 * S.v l j) := by
  unfold tangentProjection leftSingularProjection rightSingularProjection
    twoSidedSingularProjection coordinateMatrix
  simp only [Matrix.add_apply, Matrix.sub_apply]
  congr 1
  · congr 1
    · rw [Finset.sum_eq_single w1]
      · by_cases hb : j = w2 <;> simp [hb]
      · intro aa _ haa; simp [haa]
      · intro h; exact absurd (Finset.mem_univ w1) h
    · rw [Finset.sum_eq_single w2]
      · by_cases ha : i = w1 <;> simp [ha]
      · intro bb _ hbb; simp [hbb]
      · intro h; exact absurd (Finset.mem_univ w2) h
  · rw [Finset.sum_eq_single w1]
    · rw [Finset.sum_eq_single w2]
      · simp
      · intro bb _ hbb; simp [hbb]
      · intro h; exact absurd (Finset.mem_univ w2) h
    · intro aa _ haa
      apply Finset.sum_eq_zero
      intro bb _
      rw [if_neg (by rintro ⟨h1,_⟩; exact haa h1)]; ring
    · intro h; exact absurd (Finset.mem_univ w1) h

lemma PT_entry_eq_sum' (S : SVD M r) (X : RealMatrix n1 n2) (i : Fin n1) (j : Fin n2) :
    (tangentProjection S X) i j
      = ∑ w : Fin n1 × Fin n2, X w.1 w.2 * (tangentProjection S (coordinateMatrix w.1 w.2)) i j := by
  rw [PT_X_entry']
  rw [Fintype.sum_prod_type]
  simp only [PT_coord_entry']
  rw [show (∑ x : Fin n1, ∑ y : Fin n2, X x y *
        ((if j = y then (∑ k : Fin r, S.u k i * S.u k x) else 0)
          + (if i = x then (∑ l : Fin r, S.v l y * S.v l j) else 0)
          - (∑ k : Fin r, S.u k i * S.u k x) * (∑ l : Fin r, S.v l y * S.v l j)))
      = (∑ x : Fin n1, ∑ y : Fin n2, X x y * (if j = y then (∑ k : Fin r, S.u k i * S.u k x) else 0))
        + (∑ x : Fin n1, ∑ y : Fin n2, X x y * (if i = x then (∑ l : Fin r, S.v l y * S.v l j) else 0))
        - (∑ x : Fin n1, ∑ y : Fin n2, X x y * ((∑ k : Fin r, S.u k i * S.u k x) * (∑ l : Fin r, S.v l y * S.v l j))) from by
    simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib]]
  congr 1
  congr 1
  · rw [Finset.sum_comm]
    rw [Finset.sum_eq_single j]
    · apply Finset.sum_congr rfl; intro x _; simp; ring
    · intro y _ hy
      apply Finset.sum_eq_zero; intro x _; rw [if_neg (by exact fun h => hy h.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ j) h
  · rw [Finset.sum_eq_single i]
    · apply Finset.sum_congr rfl; intro y _; simp
    · intro x _ hx
      apply Finset.sum_eq_zero; intro y _; rw [if_neg (by exact fun h => hx h.symm)]; ring
    · intro h; exact absurd (Finset.mem_univ i) h
  · apply Finset.sum_congr rfl; intro x _
    apply Finset.sum_congr rfl; intro y _; ring

lemma kernel_eq_entry' (S : SVD M r) (a : Fin n1) (b : Fin n2) (i : Fin n1) (j : Fin n2) :
    tangentCoordinateKernel S a b i j
      = (tangentProjection S (coordinateMatrix a b)) i j := by
  unfold tangentCoordinateKernel matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro q _ hq; simp [hq]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro pp _ hp
    apply Finset.sum_eq_zero
    intro q _
    rw [if_neg]
    · ring
    · rintro ⟨h1, _⟩; exact hp h1
  · intro h; exact absurd (Finset.mem_univ i) h

/-! ### Entry of D + O. -/
lemma DO_entry (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (i : Fin n1) (j : Fin n2) :
    (linearNeumannDiagonalContribution Omega S p
      + linearNeumannOffDiagonalContribution Omega S p) i j
    = ∑ w2 : Fin n1 × Fin n2, (p⁻¹)^2 *
        (centeredIndicator Omega p i j * centeredIndicator Omega p w2.1 w2.2 *
          signMatrix S w2.1 w2.2 * tangentCoordinateKernel S w2.1 w2.2 i j) := by
  unfold linearNeumannDiagonalContribution linearNeumannOffDiagonalContribution
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, Matrix.sum_apply]
  -- diagonal part (post-simp form: p⁻² * ∑_w (...) * coordMat w i j)
  have hdiag : (∑ w : Fin n1 × Fin n2,
        (centeredIndicator Omega p w.1 w.2) ^ 2 * signMatrix S w.1 w.2 *
          tangentCoordinateKernel S w.1 w.2 w.1 w.2 * coordinateMatrix w.1 w.2 i j)
      = centeredIndicator Omega p i j ^ 2 * signMatrix S i j
          * tangentCoordinateKernel S i j i j := by
    rw [Finset.sum_eq_single (i, j)]
    · simp [coordinateMatrix]
    · intro w _ hw
      rw [show coordinateMatrix w.1 w.2 i j = 0 from by
        unfold coordinateMatrix; rw [if_neg]; rintro ⟨h1,h2⟩; exact hw (by ext <;> simp [h1,h2])]
      ring
    · intro h; exact absurd (Finset.mem_univ (i,j)) h
  rw [hdiag]
  -- off term in fully-distributed form (i j inside both sums)
  rw [show (∑ x : Fin n1 × Fin n2, ∑ c : Fin n1 × Fin n2,
        ((if x = c then (0 : RealMatrix n1 n2) else
          (centeredIndicator Omega p x.1 x.2 * centeredIndicator Omega p c.1 c.2 *
            signMatrix S c.1 c.2 * tangentCoordinateKernel S c.1 c.2 x.1 x.2)
        • coordinateMatrix x.1 x.2) i j))
      = ∑ w2 : Fin n1 × Fin n2,
          (if (i,j) = w2 then 0 else
            centeredIndicator Omega p i j * centeredIndicator Omega p w2.1 w2.2 *
              signMatrix S w2.1 w2.2 * tangentCoordinateKernel S w2.1 w2.2 i j) from by
    rw [Finset.sum_eq_single (i,j)]
    · apply Finset.sum_congr rfl; intro w2 _
      by_cases h : (i,j) = w2
      · simp [h]
      · rw [if_neg h, if_neg h]
        simp only [Matrix.smul_apply, smul_eq_mul]
        rw [show coordinateMatrix (i,j).1 (i,j).2 i j = 1 from by simp [coordinateMatrix]]
        ring
    · intro w1 _ hw1
      apply Finset.sum_eq_zero; intro w2 _
      by_cases h : w1 = w2
      · simp [h]
      · rw [if_neg h]
        simp only [Matrix.smul_apply, smul_eq_mul]
        rw [show coordinateMatrix w1.1 w1.2 i j = 0 from by
          unfold coordinateMatrix; rw [if_neg]; rintro ⟨h1,h2⟩; exact hw1 (by ext <;> simp [h1,h2])]
        ring
    · intro h; exact absurd (Finset.mem_univ (i,j)) h]
  -- Goal: p⁻²*diagterm + p⁻²*(∑ if (i,j)=w2 then 0 else f w2) = ∑_{w2} p⁻²*(f w2)
  -- Rewrite off-sum to ∑_{erase} f.
  rw [show (∑ w2 : Fin n1 × Fin n2,
        (if (i,j) = w2 then 0 else
          centeredIndicator Omega p i j * centeredIndicator Omega p w2.1 w2.2 *
            signMatrix S w2.1 w2.2 * tangentCoordinateKernel S w2.1 w2.2 i j))
      = ∑ w2 ∈ (Finset.univ.erase (i,j)),
          (centeredIndicator Omega p i j * centeredIndicator Omega p w2.1 w2.2 *
            signMatrix S w2.1 w2.2 * tangentCoordinateKernel S w2.1 w2.2 i j) from by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (i,j))]
    rw [if_pos rfl, add_zero]
    apply Finset.sum_congr rfl; intro w2 hw2
    rw [if_neg]
    intro h; rw [Finset.mem_erase] at hw2; exact hw2.1 h.symm]
  -- Split RHS full sum at (i,j).
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (i,j))]
  rw [Finset.mul_sum]
  -- Goal: p⁻²*diagterm + (∑_{erase} p⁻²*f) = (∑_{erase} p⁻²*f) + p⁻²*f(i,j)
  rw [add_comm (∑ x ∈ Finset.univ.erase (i,j), (p⁻¹)^2 * _)]
  congr 1
  ring

/-! Hadamard matrix G_ab = ξ_ab * E_ab. -/
noncomputable def Gmat (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) : RealMatrix n1 n2 :=
  fun a b => centeredIndicator Omega p a b * signMatrix S a b

/-- (D+O)_ij = p⁻² * ξ_ij * (P_T G)_ij. -/
lemma DO_entry_PTG (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (i : Fin n1) (j : Fin n2) :
    (linearNeumannDiagonalContribution Omega S p
      + linearNeumannOffDiagonalContribution Omega S p) i j
    = (p⁻¹)^2 * (centeredIndicator Omega p i j * (tangentProjection S (Gmat S Omega p)) i j) := by
  rw [DO_entry]
  rw [PT_entry_eq_sum']
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro w2 _
  rw [← kernel_eq_entry']
  unfold Gmat
  ring

/-! ### sign-matrix & projection lemmas (from toolkit). -/
theorem signMatrix_apply' (S : SVD M r) (i : Fin n1) (j : Fin n2) :
    signMatrix S i j = ∑ k : Fin r, S.u k i * S.v k j := by
  unfold signMatrix
  rw [Matrix.sum_apply]
  apply Finset.sum_congr rfl; intro k _
  rw [Matrix.vecMulVec_apply]

theorem leftSingularProjection_signMatrix' (S : SVD M r) :
    leftSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  rw [signMatrix_apply']
  unfold leftSingularProjection
  rw [Finset.sum_congr rfl (fun a _ => by rw [signMatrix_apply' S a j])]
  have e1 : (∑ a : Fin n1, (∑ k : Fin r, S.u k i * S.u k a) * (∑ l : Fin r, S.u l a * S.v l j))
      = ∑ a : Fin n1, ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j) := by
    apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
  rw [e1, Finset.sum_comm]
  have e2 : (∑ k : Fin r, ∑ a : Fin n1, ∑ l : Fin r, (S.u k i * S.u k a) * (S.u l a * S.v l j))
      = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n1, S.u k a * S.u l a) := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  rw [e2]
  have e3 : (∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ a : Fin n1, S.u k a * S.u l a))
      = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (if k = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
    rw [S.u_orthonormal k l]
  rw [e3]
  apply Finset.sum_congr rfl; intro k _
  have : (∑ l : Fin r, S.u k i * S.v l j * (if k = l then 1 else 0))
      = ∑ l : Fin r, (if k = l then S.u k i * S.v l j else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp

theorem rightSingularProjection_signMatrix' (S : SVD M r) :
    rightSingularProjection S (signMatrix S) = signMatrix S := by
  funext i j
  rw [signMatrix_apply']
  unfold rightSingularProjection
  rw [Finset.sum_congr rfl (fun b _ => by rw [signMatrix_apply' S i b])]
  have e1 : (∑ b : Fin n2, (∑ k : Fin r, S.u k i * S.v k b) * (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ b : Fin n2, ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v k b) * (S.v l b * S.v l j) := by
    apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul_sum]
  rw [e1, Finset.sum_comm]
  have e2 : (∑ k : Fin r, ∑ b : Fin n2, ∑ l : Fin r, (S.u k i * S.v k b) * (S.v l b * S.v l j))
      = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ b : Fin n2, S.v k b * S.v l b) := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
  rw [e2]
  have e3 : (∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (∑ b : Fin n2, S.v k b * S.v l b))
      = ∑ k : Fin r, ∑ l : Fin r, (S.u k i * S.v l j) * (if k = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _
    rw [S.v_orthonormal k l]
  rw [e3]
  apply Finset.sum_congr rfl; intro k _
  have : (∑ l : Fin r, S.u k i * S.v l j * (if k = l then 1 else 0))
      = ∑ l : Fin r, (if k = l then S.u k i * S.v l j else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp

theorem twoSidedSingularProjection_signMatrix' (S : SVD M r) :
    twoSidedSingularProjection S (signMatrix S) = signMatrix S := by
  refine Eq.trans ?_ (leftSingularProjection_signMatrix' S)
  funext i j
  unfold twoSidedSingularProjection leftSingularProjection
  apply Finset.sum_congr rfl; intro a _
  have hfac : (∑ b : Fin n2,
        (∑ k : Fin r, S.u k i * S.u k a) * signMatrix S a b * (∑ l : Fin r, S.v l b * S.v l j))
      = (∑ k : Fin r, S.u k i * S.u k a)
          * (∑ b : Fin n2, signMatrix S a b * (∑ l : Fin r, S.v l b * S.v l j)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro b _; ring
  rw [hfac]
  congr 1
  rw [signMatrix_apply']
  conv_lhs => enter [2, b]; rw [signMatrix_apply' S a b]
  have e1 : (∑ b : Fin n2, (∑ m : Fin r, S.u m a * S.v m b) * (∑ l : Fin r, S.v l b * S.v l j))
      = ∑ b : Fin n2, ∑ m : Fin r, ∑ l : Fin r, (S.u m a * S.v l j) * (S.v m b * S.v l b) := by
    apply Finset.sum_congr rfl; intro b _; rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro l _; ring
  rw [e1, Finset.sum_comm]
  have e2 : (∑ m : Fin r, ∑ b : Fin n2, ∑ l : Fin r, (S.u m a * S.v l j) * (S.v m b * S.v l b))
      = ∑ m : Fin r, ∑ l : Fin r, (S.u m a * S.v l j) * (∑ b : Fin n2, S.v m b * S.v l b) := by
    apply Finset.sum_congr rfl; intro m _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]
  rw [e2]
  have e3 : (∑ m : Fin r, ∑ l : Fin r, (S.u m a * S.v l j) * (∑ b : Fin n2, S.v m b * S.v l b))
      = ∑ m : Fin r, ∑ l : Fin r, (S.u m a * S.v l j) * (if m = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro m _; apply Finset.sum_congr rfl; intro l _
    rw [S.v_orthonormal m l]
  rw [e3]
  apply Finset.sum_congr rfl; intro m _
  have : (∑ l : Fin r, S.u m a * S.v l j * (if m = l then 1 else 0))
      = ∑ l : Fin r, (if m = l then S.u m a * S.v l j else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : m = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp

theorem tangentProjection_signMatrix' (S : SVD M r) :
    tangentProjection S (signMatrix S) = signMatrix S := by
  unfold tangentProjection
  rw [leftSingularProjection_signMatrix', rightSingularProjection_signMatrix',
    twoSidedSingularProjection_signMatrix']
  abel

/-- P_Ω E = G + p • E. -/
theorem samplingProjection_signMatrix_eq (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) :
    samplingProjection Omega (signMatrix S) = Gmat S Omega p + p • signMatrix S := by
  funext i j
  unfold samplingProjection Gmat centeredIndicator
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : (i, j) ∈ Omega <;> simp [h] <;> ring

/-- linearity: per-projection smul. -/
theorem leftSingularProjection_smul' (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    leftSingularProjection S (c • X) = c • leftSingularProjection S X := by
  funext i j; unfold leftSingularProjection
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _; ring
theorem rightSingularProjection_smul' (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    rightSingularProjection S (c • X) = c • rightSingularProjection S X := by
  funext i j; unfold rightSingularProjection
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro b _; ring
theorem twoSidedSingularProjection_smul' (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (c • X) = c • twoSidedSingularProjection S X := by
  funext i j; unfold twoSidedSingularProjection
  simp only [Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _; apply Finset.sum_congr rfl; intro b _; ring
theorem tangentProjection_smul' (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    tangentProjection S (c • X) = c • tangentProjection S X := by
  unfold tangentProjection
  rw [leftSingularProjection_smul', rightSingularProjection_smul', twoSidedSingularProjection_smul',
    smul_sub, smul_add]

theorem leftSingularProjection_add' (S : SVD M r) (X Y : RealMatrix n1 n2) :
    leftSingularProjection S (X + Y) = leftSingularProjection S X + leftSingularProjection S Y := by
  funext i j; unfold leftSingularProjection
  rw [Matrix.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _; rw [Matrix.add_apply]; ring
theorem rightSingularProjection_add' (S : SVD M r) (X Y : RealMatrix n1 n2) :
    rightSingularProjection S (X + Y) = rightSingularProjection S X + rightSingularProjection S Y := by
  funext i j; unfold rightSingularProjection
  rw [Matrix.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _; rw [Matrix.add_apply]; ring
theorem twoSidedSingularProjection_add' (S : SVD M r) (X Y : RealMatrix n1 n2) :
    twoSidedSingularProjection S (X + Y) = twoSidedSingularProjection S X + twoSidedSingularProjection S Y := by
  funext i j; unfold twoSidedSingularProjection
  rw [Matrix.add_apply, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro a _; rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro b _; rw [Matrix.add_apply]; ring
theorem tangentProjection_add' (S : SVD M r) (X Y : RealMatrix n1 n2) :
    tangentProjection S (X + Y) = tangentProjection S X + tangentProjection S Y := by
  unfold tangentProjection
  rw [leftSingularProjection_add', rightSingularProjection_add', twoSidedSingularProjection_add']
  abel

/-- Y₁ = neumannIterate 1 = -p⁻¹ • P_T G  (for p ≠ 0). -/
theorem neumannIterate_one_eq (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : p ≠ 0) :
    neumannIterate Omega S p 1 = (-p⁻¹) • tangentProjection S (Gmat S Omega p) := by
  unfold neumannIterate
  rw [Function.iterate_one]
  unfold neumannErrorOperator
  rw [tangentProjection_signMatrix']
  rw [samplingProjection_signMatrix_eq S Omega p]
  rw [tangentProjection_add', tangentProjection_smul', tangentProjection_signMatrix']
  rw [smul_add, smul_smul]
  funext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, neg_mul]
  rw [inv_mul_cancel₀ hp]; ring

/-- idempotence of P_T (needed: P_T(P_T G) = P_T G). We get it from kernel_eq_entry +
PT_entry_eq_sum, but simplest: prove on the specific G via entrywise. We just need that
tangentProjection S Y1 = Y1.  Since Y1 = (-p⁻¹) • P_T G, use P_T idempotent. -/
theorem tangentProjection_idem (S : SVD M r) (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X :=
  TangentAlgebra.tangent_idem S X

/-- Sub linearity. -/
theorem tangentProjection_sub' (S : SVD M r) (X Y : RealMatrix n1 n2) :
    tangentProjection S (X - Y) = tangentProjection S X - tangentProjection S Y := by
  have : X - Y = X + (-1 : ℝ) • Y := by
    funext i j; simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]; ring
  rw [this, tangentProjection_add', tangentProjection_smul']
  funext i j; simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]; ring
theorem normalProjection_smul' (S : SVD M r) (c : ℝ) (X : RealMatrix n1 n2) :
    normalProjection S (c • X) = c • normalProjection S X := by
  unfold normalProjection; rw [tangentProjection_smul', smul_sub]
theorem normalProjection_sub' (S : SVD M r) (X Y : RealMatrix n1 n2) :
    normalProjection S (X - Y) = normalProjection S X - normalProjection S Y := by
  unfold normalProjection; rw [tangentProjection_sub']; abel
theorem normalProjection_signMatrix' (S : SVD M r) :
    normalProjection S (signMatrix S) = 0 := by
  unfold normalProjection; rw [tangentProjection_signMatrix']; abel
/-- P_Tperp kills any P_T Y (normalProjection of a tangent matrix). -/
theorem normalProjection_tangent_zero (S : SVD M r) (Y : RealMatrix n1 n2) :
    normalProjection S (tangentProjection S Y) = 0 := by
  unfold normalProjection; rw [tangentProjection_idem]; abel

/-- centered sampling fluctuation entry. -/
theorem cSF_entry (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (Y : RealMatrix n1 n2)
    (i : Fin n1) (j : Fin n2) :
    (centeredSamplingFluctuation Omega p Y) i j
      = p⁻¹ * (centeredIndicator Omega p i j) * Y i j := by
  unfold centeredSamplingFluctuation samplingProjection centeredIndicator
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  by_cases h : (i, j) ∈ Omega <;> simp [h] <;> ring

/-- THE reduction sign-check: neumannCertificateTerm 1 vs normalProjection(cSF Y₁). -/
theorem certTerm1_eq_normalProj_cSF (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (hp : p ≠ 0) :
    neumannCertificateTerm Omega S p 1
      = normalProjection S (centeredSamplingFluctuation Omega p (neumannIterate Omega S p 1)) := by
  unfold neumannCertificateTerm centeredSamplingFluctuation
  -- LHS: p⁻¹ • normalProjection (P_Ω (P_T Y₁))
  -- inner P_T Y₁ = Y₁ since Y₁ ∈ T.
  have hY1T : tangentProjection S (neumannIterate Omega S p 1) = neumannIterate Omega S p 1 := by
    rw [neumannIterate_one_eq S Omega p hp, tangentProjection_smul', tangentProjection_idem]
  rw [hY1T]
  -- RHS: normalProjection (p⁻¹ • (P_Ω Y₁ - p • Y₁))
  rw [normalProjection_smul', normalProjection_sub', normalProjection_smul']
  -- normalProjection (p • Y₁) = p • normalProjection Y₁ ; and normalProjection Y₁ = 0 (Y₁ ∈ T)
  rw [show normalProjection S (neumannIterate Omega S p 1) = 0 from by
    conv_lhs => rw [← hY1T]; exact normalProjection_tangent_zero S _]
  rw [smul_zero, sub_zero]

/-- cSF Y₁ = -(D+O) entrywise (p ≠ 0). -/
theorem cSF_Y1_eq_neg_DO (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : p ≠ 0) :
    centeredSamplingFluctuation Omega p (neumannIterate Omega S p 1)
      = - (linearNeumannDiagonalContribution Omega S p
          + linearNeumannOffDiagonalContribution Omega S p) := by
  funext i j
  rw [cSF_entry, neumannIterate_one_eq S Omega p hp]
  simp only [Matrix.neg_apply, Matrix.smul_apply, smul_eq_mul]
  rw [DO_entry_PTG]
  ring

/-- THEREFORE the stated theorem holds iff normalProjection(D+O)=0, i.e.
    neumannCertificateTerm 1 = -(normalProjection (D+O)).  The platform target uses +. -/
theorem certTerm1_eq_NEG_normalProj_DO (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (hp : p ≠ 0) :
    neumannCertificateTerm Omega S p 1
      = - normalProjection S (linearNeumannDiagonalContribution Omega S p
          + linearNeumannOffDiagonalContribution Omega S p) := by
  rw [certTerm1_eq_normalProj_cSF S Omega p hp, cSF_Y1_eq_neg_DO S Omega p hp]
  have hPT0 : tangentProjection S (0 : RealMatrix n1 n2) = 0 := by
    funext i j
    unfold tangentProjection leftSingularProjection rightSingularProjection twoSidedSingularProjection
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply]
  have hNP0 : normalProjection S (0 : RealMatrix n1 n2) = 0 := by
    unfold normalProjection; rw [hPT0]; abel
  have hneg : ∀ X : RealMatrix n1 n2, normalProjection S (-X) = - normalProjection S X := by
    intro X
    have hx : (-X : RealMatrix n1 n2) = (0 : RealMatrix n1 n2) - X := by
      funext i j; simp [Matrix.sub_apply, Matrix.neg_apply, Matrix.zero_apply]
    rw [hx, normalProjection_sub', hNP0]; abel
  rw [hneg]


/-- p=0 edges. -/
theorem certTerm1_p0 (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) :
    neumannCertificateTerm Omega S 0 1 = 0 := by
  unfold neumannCertificateTerm; simp
theorem linDiag_p0 (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) :
    linearNeumannDiagonalContribution Omega S 0 = 0 := by
  unfold linearNeumannDiagonalContribution; simp
theorem linOff_p0 (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) :
    linearNeumannOffDiagonalContribution Omega S 0 = 0 := by
  unfold linearNeumannOffDiagonalContribution; simp
theorem normalProjection_zero'' (S : SVD M r) :
    normalProjection S (0 : RealMatrix n1 n2) = 0 := by
  unfold normalProjection
  rw [show tangentProjection S (0 : RealMatrix n1 n2) = 0 from by
    funext i j; unfold tangentProjection leftSingularProjection rightSingularProjection twoSidedSingularProjection
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply]]
  abel

end MatrixCompletion

open MatrixCompletion

/-- PROOF of the sign-corrected first Neumann certificate identity (CR §6.2 eq 6.8).
cert₁ = −normalProjection(D+O): H(E) = −p⁻¹·P_T G gives cSF(H(E)) = −(D+O); the single
H-application's −p⁻¹ flip makes the sign negative (cf. the k=2 case is +). -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) :
    neumannCertificateTerm Omega S p 1 =
      -normalProjection S
        (linearNeumannDiagonalContribution Omega S p +
          linearNeumannOffDiagonalContribution Omega S p) := by
  by_cases hp : p = 0
  · subst hp
    rw [certTerm1_p0, linDiag_p0, linOff_p0, add_zero, normalProjection_zero'', neg_zero]
  · exact certTerm1_eq_NEG_normalProj_DO S Omega p hp

#print axioms solution
