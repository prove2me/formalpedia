-- Prove2me | solution 1 for second_neumann_certificate_term_as_normal_projection_of_quadratic_correction
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-22T05:35:05.639325+00:00
-- url     : https://prove2.me/submissions/c9ee8ab3-ad81-4ee4-bce0-87995fe7acd7

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


/-! ## Node 2 (quadratic, k=2) lemmas. -/

/-- ξ-Hadamard of a matrix. -/
noncomputable def xiHad (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (X : RealMatrix n1 n2) :
    RealMatrix n1 n2 := fun a b => centeredIndicator Omega p a b * X a b

theorem neumannErrorOperator_on_tangent (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (Y : RealMatrix n1 n2) (hY : tangentProjection S Y = Y) :
    neumannErrorOperator Omega S p Y = Y - p⁻¹ • tangentProjection S (samplingProjection Omega Y) := by
  unfold neumannErrorOperator
  rw [hY]

theorem samplingProjection_eq_xiHad (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (Y : RealMatrix n1 n2) :
    samplingProjection Omega Y = xiHad Omega p Y + p • Y := by
  funext i j
  unfold samplingProjection xiHad centeredIndicator
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  by_cases h : (i, j) ∈ Omega <;> simp [h] <;> ring

theorem neumannIterate_two_eq (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : p ≠ 0) :
    neumannIterate Omega S p 2
      = (p⁻¹)^2 • tangentProjection S (xiHad Omega p (tangentProjection S (Gmat S Omega p))) := by
  have h2 : neumannIterate Omega S p 2
      = neumannErrorOperator Omega S p (neumannIterate Omega S p 1) := by
    unfold neumannIterate
    rw [show (2 : ℕ) = 1 + 1 from rfl, Function.iterate_add_apply, Function.iterate_one]
  rw [h2]
  have hY1 := neumannIterate_one_eq S Omega p hp
  have hY1T : tangentProjection S (neumannIterate Omega S p 1) = neumannIterate Omega S p 1 := by
    rw [hY1, tangentProjection_smul', tangentProjection_idem]
  rw [neumannErrorOperator_on_tangent S Omega p _ hY1T]
  rw [hY1]
  rw [show samplingProjection Omega ((-p⁻¹) • tangentProjection S (Gmat S Omega p))
      = (-p⁻¹) • samplingProjection Omega (tangentProjection S (Gmat S Omega p)) from by
    funext i j; unfold samplingProjection
    simp only [Matrix.smul_apply, smul_eq_mul]; by_cases h : (i,j) ∈ Omega <;> simp [h]]
  rw [samplingProjection_eq_xiHad Omega p]
  rw [tangentProjection_smul', tangentProjection_add', tangentProjection_smul']
  rw [show tangentProjection S (tangentProjection S (Gmat S Omega p)) = tangentProjection S (Gmat S Omega p) from tangentProjection_idem S _]
  funext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, neg_mul]
  -- goal: -(p⁻¹ * A) - p⁻¹ * (-(p⁻¹ * (B + p * A))) = p⁻¹^2 * B
  generalize (tangentProjection S (Gmat S Omega p)) i j = A
  generalize (tangentProjection S (xiHad Omega p (tangentProjection S (Gmat S Omega p)))) i j = B
  field_simp
  ring

/-- Reduction for k=2: neumannCertificateTerm 2 = normalProjection(cSF(H²(E))). -/
theorem certTerm2_eq_normalProj_cSF (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (hp : p ≠ 0) :
    neumannCertificateTerm Omega S p 2
      = normalProjection S (centeredSamplingFluctuation Omega p (neumannIterate Omega S p 2)) := by
  unfold neumannCertificateTerm centeredSamplingFluctuation
  have hY2T : tangentProjection S (neumannIterate Omega S p 2) = neumannIterate Omega S p 2 := by
    rw [neumannIterate_two_eq S Omega p hp, tangentProjection_smul', tangentProjection_idem]
  rw [hY2T]
  rw [normalProjection_smul', normalProjection_sub', normalProjection_smul']
  rw [show normalProjection S (neumannIterate Omega S p 2) = 0 from by
    conv_lhs => rw [← hY2T]; exact normalProjection_tangent_zero S _]
  rw [smul_zero, sub_zero]

/-- cSF(H²(E)) entry = p⁻³ ξ_ij (P_T(ξ⊙P_T G))_ij. -/
theorem cSF_Y2_entry (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : p ≠ 0)
    (i : Fin n1) (j : Fin n2) :
    (centeredSamplingFluctuation Omega p (neumannIterate Omega S p 2)) i j
      = (p⁻¹)^3 * (centeredIndicator Omega p i j
          * (tangentProjection S (xiHad Omega p (tangentProjection S (Gmat S Omega p)))) i j) := by
  rw [cSF_entry, neumannIterate_two_eq S Omega p hp]
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring


/-! ## Generic entry-extraction helpers for contribution sums. -/

/-- single sum: (Σ_w c(w) • e_w) i j = c(i,j). -/
lemma single_sum_entry (c : Fin n1 × Fin n2 → ℝ) (i : Fin n1) (j : Fin n2) :
    (∑ w : Fin n1 × Fin n2, c w • coordinateMatrix w.1 w.2) i j = c (i, j) := by
  rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
  · simp only [Matrix.smul_apply, smul_eq_mul]
    rw [show coordinateMatrix (i,j).1 (i,j).2 i j = 1 from by simp [coordinateMatrix]]; ring
  · intro w _ hw
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [show coordinateMatrix w.1 w.2 i j = 0 from by
      unfold coordinateMatrix; rw [if_neg]; rintro ⟨h1,h2⟩; exact hw (by ext <;> simp [h1,h2])]; ring
  · intro h; exact absurd (Finset.mem_univ (i,j)) h

/-- double sum with w1-outer coordinate: (Σ_{w1}Σ_{w2} F w1 w2 • e_{w1}) i j = Σ_{w2} F (i,j) w2. -/
lemma double_sum_entry (F : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ) (i : Fin n1) (j : Fin n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, F w1 w2 • coordinateMatrix w1.1 w1.2) i j
      = ∑ w2 : Fin n1 × Fin n2, F (i, j) w2 := by
  rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
  · rw [Matrix.sum_apply]; apply Finset.sum_congr rfl; intro w2 _
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [show coordinateMatrix (i,j).1 (i,j).2 i j = 1 from by simp [coordinateMatrix]]; ring
  · intro w1 _ hw1
    rw [Matrix.sum_apply]; apply Finset.sum_eq_zero; intro w2 _
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [show coordinateMatrix w1.1 w1.2 i j = 0 from by
      unfold coordinateMatrix; rw [if_neg]; rintro ⟨h1,h2⟩; exact hw1 (by ext <;> simp [h1,h2])]; ring
  · intro h; exact absurd (Finset.mem_univ (i,j)) h

/-- triple sum with w1-outer coordinate. -/
lemma triple_sum_entry (F : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ)
    (i : Fin n1) (j : Fin n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        F w1 w2 w3 • coordinateMatrix w1.1 w1.2) i j
      = ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2, F (i, j) w2 w3 := by
  rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
  · rw [Matrix.sum_apply]; apply Finset.sum_congr rfl; intro w2 _
    rw [Matrix.sum_apply]; apply Finset.sum_congr rfl; intro w3 _
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [show coordinateMatrix (i,j).1 (i,j).2 i j = 1 from by simp [coordinateMatrix]]; ring
  · intro w1 _ hw1
    rw [Matrix.sum_apply]; apply Finset.sum_eq_zero; intro w2 _
    rw [Matrix.sum_apply]; apply Finset.sum_eq_zero; intro w3 _
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [show coordinateMatrix w1.1 w1.2 i j = 0 from by
      unfold coordinateMatrix; rw [if_neg]; rintro ⟨h1,h2⟩; exact hw1 (by ext <;> simp [h1,h2])]; ring
  · intro h; exact absurd (Finset.mem_univ (i,j)) h


/-! ## The (w2,w3) partition into 5 coincidence classes. -/

/-- Σ_{w2,w3} g w2 w3 splits into the 5 index-coincidence regions (c = the fixed (i,j)=w1). -/
lemma double_partition (g : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ) (c : Fin n1 × Fin n2) :
    (∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2, g w2 w3)
      = g c c
        + (∑ w2 ∈ Finset.univ.erase c, g w2 w2)
        + (∑ w2 ∈ Finset.univ.erase c, g w2 c)
        + (∑ w3 ∈ Finset.univ.erase c, g c w3)
        + (∑ w2 ∈ Finset.univ.erase c, ∑ w3 ∈ (Finset.univ.erase c).erase w2, g w2 w3) := by
  -- split outer at c
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c)]
  -- the c-term (w2=c): Σ_{w3} g c w3 = g c c + Σ_{w3≠c} g c w3
  rw [show (∑ w3 : Fin n1 × Fin n2, g c w3)
      = g c c + ∑ w3 ∈ Finset.univ.erase c, g c w3 from by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c)]; ring]
  -- for each w2≠c: Σ_{w3} g w2 w3 = g w2 c + g w2 w2 + Σ_{w3 ≠ c, w3 ≠ w2} g w2 w3
  rw [show (∑ w2 ∈ Finset.univ.erase c, ∑ w3 : Fin n1 × Fin n2, g w2 w3)
      = (∑ w2 ∈ Finset.univ.erase c, g w2 c)
        + (∑ w2 ∈ Finset.univ.erase c, g w2 w2)
        + (∑ w2 ∈ Finset.univ.erase c, ∑ w3 ∈ (Finset.univ.erase c).erase w2, g w2 w3) from by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro w2 hw2
    have hw2c : w2 ≠ c := (Finset.mem_erase.mp hw2).1
    -- Σ_{w3} g w2 w3 = g w2 c + (g w2 w2 + Σ_{w3 ≠c,≠w2} g w2 w3)
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ c)]
    -- now inner over erase c, plus g w2 c. peel w2 from erase c (w2 ∈ erase c since w2≠c)
    rw [show (∑ w3 ∈ Finset.univ.erase c, g w2 w3)
        = g w2 w2 + ∑ w3 ∈ (Finset.univ.erase c).erase w2, g w2 w3 from by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_erase.mpr ⟨hw2c, Finset.mem_univ w2⟩)]; ring]
    ring]
  ring


/-! ## Contribution entry lemmas (each = p⁻³ • region term). -/

/-- abbreviation g for the double-sum integrand at fixed (i,j). -/
noncomputable def gfun (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ)
    (i : Fin n1) (j : Fin n2) (w2 w3 : Fin n1 × Fin n2) : ℝ :=
  centeredIndicator Omega p w2.1 w2.2 * centeredIndicator Omega p w3.1 w3.2 *
    signMatrix S w3.1 w3.2 * tangentCoordinateKernel S w3.1 w3.2 w2.1 w2.2 *
      tangentCoordinateKernel S w2.1 w2.2 i j

theorem allEqual_entry (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (i : Fin n1) (j : Fin n2) :
    (quadraticNeumannAllEqualContribution Omega S p) i j
      = (p⁻¹)^3 * (centeredIndicator Omega p i j * gfun S Omega p i j (i,j) (i,j)) := by
  unfold quadraticNeumannAllEqualContribution
  rw [Matrix.smul_apply, smul_eq_mul]
  rw [single_sum_entry (fun w => (centeredIndicator Omega p w.1 w.2)^3 * signMatrix S w.1 w.2 *
      tangentCoordinateKernel S w.1 w.2 w.1 w.2 * tangentCoordinateKernel S w.1 w.2 w.1 w.2) i j]
  unfold gfun
  ring

/-- double-sum entry, matrix-valued if-then-else form. -/
lemma double_sum_entry_ite (F : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ) (i : Fin n1) (j : Fin n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2,
        (if w1 = w2 then (0:RealMatrix n1 n2) else (F w1 w2) • coordinateMatrix w1.1 w1.2)) i j
      = ∑ w2 : Fin n1 × Fin n2, if (i,j) = w2 then (0:ℝ) else F (i,j) w2 := by
  rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
  · rw [Matrix.sum_apply]; apply Finset.sum_congr rfl; intro w2 _
    by_cases h : (i,j) = w2
    · simp [h]
    · rw [if_neg h, if_neg h]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [show coordinateMatrix (i,j).1 (i,j).2 i j = 1 from by simp [coordinateMatrix]]; ring
  · intro w1 _ hw1
    rw [Matrix.sum_apply]; apply Finset.sum_eq_zero; intro w2 _
    by_cases h : w1 = w2
    · simp [h]
    · rw [if_neg h]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [show coordinateMatrix w1.1 w1.2 i j = 0 from by
        unfold coordinateMatrix; rw [if_neg]; rintro ⟨h1,h2⟩; exact hw1 (by ext <;> simp [h1,h2])]; ring
  · intro h; exact absurd (Finset.mem_univ (i,j)) h

theorem first_entry (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (i : Fin n1) (j : Fin n2) :
    (quadraticNeumannFirstIndexDistinctContribution Omega S p) i j
      = (p⁻¹)^3 * (centeredIndicator Omega p i j
          * ∑ w2 ∈ Finset.univ.erase (i,j), gfun S Omega p i j w2 w2) := by
  unfold quadraticNeumannFirstIndexDistinctContribution
  rw [Matrix.smul_apply, smul_eq_mul]
  rw [double_sum_entry_ite (fun w1 w2 =>
      centeredIndicator Omega p w1.1 w1.2 * (centeredIndicator Omega p w2.1 w2.2)^2 *
        signMatrix S w2.1 w2.2 * tangentCoordinateKernel S w2.1 w2.2 w2.1 w2.2 *
          tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) i j]
  -- LHS: p⁻³ * ∑_univ (if (i,j)=w2 then 0 else c). Peel (i,j).
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (i,j)), if_pos rfl, add_zero]
  -- RHS: p⁻³ * (ξ_ij * ∑_erase gfun)
  rw [mul_comm (centeredIndicator Omega p i j), Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro w2 hw2
  rw [if_neg (by intro h; exact (Finset.mem_erase.mp hw2).1 h.symm)]
  unfold gfun; ring


theorem middle_entry (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (i : Fin n1) (j : Fin n2) :
    (quadraticNeumannMiddleIndexDistinctContribution Omega S p) i j
      = (p⁻¹)^3 * (centeredIndicator Omega p i j
          * ∑ w2 ∈ Finset.univ.erase (i,j), gfun S Omega p i j w2 (i,j)) := by
  unfold quadraticNeumannMiddleIndexDistinctContribution
  rw [Matrix.smul_apply, smul_eq_mul]
  rw [double_sum_entry_ite (fun w1 w2 =>
      (centeredIndicator Omega p w1.1 w1.2)^2 * centeredIndicator Omega p w2.1 w2.2 *
        signMatrix S w1.1 w1.2 * tangentCoordinateKernel S w1.1 w1.2 w2.1 w2.2 *
          tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) i j]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (i,j)), if_pos rfl, add_zero]
  rw [mul_comm (centeredIndicator Omega p i j), Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro w2 hw2
  rw [if_neg (by intro h; exact (Finset.mem_erase.mp hw2).1 h.symm)]
  unfold gfun; ring

theorem last_entry (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (i : Fin n1) (j : Fin n2) :
    (quadraticNeumannLastIndexDistinctContribution Omega S p) i j
      = (p⁻¹)^3 * (centeredIndicator Omega p i j
          * ∑ w3 ∈ Finset.univ.erase (i,j), gfun S Omega p i j (i,j) w3) := by
  unfold quadraticNeumannLastIndexDistinctContribution
  rw [Matrix.smul_apply, smul_eq_mul]
  rw [double_sum_entry_ite (fun w1 w3 =>
      (centeredIndicator Omega p w1.1 w1.2)^2 * centeredIndicator Omega p w3.1 w3.2 *
        signMatrix S w3.1 w3.2 * tangentCoordinateKernel S w3.1 w3.2 w1.1 w1.2 *
          tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2) i j]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (i,j)), if_pos rfl, add_zero]
  rw [mul_comm (centeredIndicator Omega p i j), Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro w3 hw3
  rw [if_neg (by intro h; exact (Finset.mem_erase.mp hw3).1 h.symm)]
  unfold gfun; ring


/-- triple-sum entry, matrix-valued if (condition w1=w2 ∨ w1=w3 ∨ w2=w3). -/
lemma triple_sum_entry_ite (F : (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → (Fin n1 × Fin n2) → ℝ)
    (i : Fin n1) (j : Fin n2) :
    (∑ w1 : Fin n1 × Fin n2, ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
        (if w1 = w2 ∨ w1 = w3 ∨ w2 = w3 then (0:RealMatrix n1 n2)
         else (F w1 w2 w3) • coordinateMatrix w1.1 w1.2)) i j
      = ∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2,
          if (i,j) = w2 ∨ (i,j) = w3 ∨ w2 = w3 then (0:ℝ) else F (i,j) w2 w3 := by
  rw [Matrix.sum_apply, Finset.sum_eq_single (i, j)]
  · rw [Matrix.sum_apply]; apply Finset.sum_congr rfl; intro w2 _
    rw [Matrix.sum_apply]; apply Finset.sum_congr rfl; intro w3 _
    by_cases h : (i,j) = w2 ∨ (i,j) = w3 ∨ w2 = w3
    · simp [h]
    · rw [if_neg h, if_neg h]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [show coordinateMatrix (i,j).1 (i,j).2 i j = 1 from by simp [coordinateMatrix]]; ring
  · intro w1 _ hw1
    rw [Matrix.sum_apply]; apply Finset.sum_eq_zero; intro w2 _
    rw [Matrix.sum_apply]; apply Finset.sum_eq_zero; intro w3 _
    by_cases h : w1 = w2 ∨ w1 = w3 ∨ w2 = w3
    · simp [h]
    · rw [if_neg h]
      simp only [Matrix.smul_apply, smul_eq_mul]
      rw [show coordinateMatrix w1.1 w1.2 i j = 0 from by
        unfold coordinateMatrix; rw [if_neg]; rintro ⟨h1,h2⟩; exact hw1 (by ext <;> simp [h1,h2])]; ring
  · intro h; exact absurd (Finset.mem_univ (i,j)) h

theorem allDistinct_entry (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (i : Fin n1) (j : Fin n2) :
    (quadraticNeumannAllDistinctContribution Omega S p) i j
      = (p⁻¹)^3 * (centeredIndicator Omega p i j
          * ∑ w2 ∈ Finset.univ.erase (i,j), ∑ w3 ∈ (Finset.univ.erase (i,j)).erase w2,
              gfun S Omega p i j w2 w3) := by
  unfold quadraticNeumannAllDistinctContribution
  rw [Matrix.smul_apply, smul_eq_mul]
  rw [triple_sum_entry_ite (fun w1 w2 w3 =>
      centeredIndicator Omega p w1.1 w1.2 * centeredIndicator Omega p w2.1 w2.2 *
        centeredIndicator Omega p w3.1 w3.2 * signMatrix S w3.1 w3.2 *
          tangentCoordinateKernel S w3.1 w3.2 w2.1 w2.2 *
            tangentCoordinateKernel S w2.1 w2.2 w1.1 w1.2) i j]
  -- Transform the double conditional sum into ξ_ij * (erase-erase region of gfun).
  congr 1
  rw [Finset.mul_sum]
  -- outer: split at (i,j); the (i,j) term vanishes (condition w1=w2)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (i,j))]
  rw [show (∑ w3 : Fin n1 × Fin n2, if (i,j) = (i,j) ∨ (i,j) = w3 ∨ (i,j) = w3 then (0:ℝ)
        else centeredIndicator Omega p (i,j).1 (i,j).2 * centeredIndicator Omega p (i,j).1 (i,j).2 *
          centeredIndicator Omega p w3.1 w3.2 * signMatrix S w3.1 w3.2 *
            tangentCoordinateKernel S w3.1 w3.2 (i,j).1 (i,j).2 *
              tangentCoordinateKernel S (i,j).1 (i,j).2 (i,j).1 (i,j).2) = 0 from by
    apply Finset.sum_eq_zero; intro w3 _; rw [if_pos (Or.inl rfl)]]
  rw [add_zero]
  apply Finset.sum_congr rfl; intro w2 hw2
  have hw2c : w2 ≠ (i,j) := (Finset.mem_erase.mp hw2).1
  rw [Finset.mul_sum]
  -- inner: split at (i,j) (vanishes: (i,j)=w3) and at w2 (vanishes: w2=w3)
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (i,j))]
  rw [if_pos (Or.inr (Or.inl rfl)), add_zero]
  rw [← Finset.sum_erase_add _ _ hw2]
  rw [if_pos (Or.inr (Or.inr rfl)), add_zero]
  apply Finset.sum_congr rfl; intro w3 hw3
  have hw3c : w3 ≠ (i,j) := (Finset.mem_erase.mp (Finset.mem_erase.mp hw3).2).1
  have hw3w2 : w3 ≠ w2 := (Finset.mem_erase.mp hw3).1
  rw [if_neg (by push_neg; exact ⟨fun h => hw2c h.symm, fun h => hw3c h.symm, fun h => hw3w2 h.symm⟩)]
  unfold gfun; ring


/-- The double sum of gfun equals (P_T (ξ ⊙ P_T G))_ij. -/
theorem gfun_double_sum_eq (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (i : Fin n1) (j : Fin n2) :
    (∑ w2 : Fin n1 × Fin n2, ∑ w3 : Fin n1 × Fin n2, gfun S Omega p i j w2 w3)
      = (tangentProjection S (xiHad Omega p (tangentProjection S (Gmat S Omega p)))) i j := by
  rw [PT_entry_eq_sum']
  apply Finset.sum_congr rfl; intro w2 _
  -- (xiHad Omega p (P_T G)) w2 = ξ_w2 * (P_T G) w2 = ξ_w2 * Σ_w3 G_w3 (P_T e_w3)_w2
  unfold xiHad
  rw [PT_entry_eq_sum' S (Gmat S Omega p) w2.1 w2.2]
  -- gfun S Omega p i j w2 w3 = ξ_w2 ξ_w3 E_w3 K(w3,w2) K(w2,ij)
  rw [← kernel_eq_entry' S w2.1 w2.2 i j]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro w3 _
  rw [← kernel_eq_entry' S w3.1 w3.2 w2.1 w2.2]
  unfold gfun Gmat
  ring

/-- MASTER: sum of the 5 quadratic contributions = cSF(H²(E)). -/
theorem sum5_eq_cSF_Y2 (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) (p : ℝ) (hp : p ≠ 0) :
    quadraticNeumannAllEqualContribution Omega S p
      + quadraticNeumannFirstIndexDistinctContribution Omega S p
      + quadraticNeumannMiddleIndexDistinctContribution Omega S p
      + quadraticNeumannLastIndexDistinctContribution Omega S p
      + quadraticNeumannAllDistinctContribution Omega S p
      = centeredSamplingFluctuation Omega p (neumannIterate Omega S p 2) := by
  funext i j
  rw [cSF_Y2_entry S Omega p hp]
  simp only [Matrix.add_apply]
  rw [allEqual_entry, first_entry, middle_entry, last_entry, allDistinct_entry]
  rw [← gfun_double_sum_eq S Omega p i j]
  rw [double_partition (gfun S Omega p i j) (i,j)]
  ring


/-- p=0 edge: each (p⁻¹)^k-scaled matrix is 0, and cert term is 0. -/
theorem certTerm2_p0 (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) :
    neumannCertificateTerm Omega S 0 2 = 0 := by
  unfold neumannCertificateTerm
  simp

theorem allEqual_p0 (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) :
    quadraticNeumannAllEqualContribution Omega S 0 = 0 := by
  unfold quadraticNeumannAllEqualContribution; simp
theorem first_p0 (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) :
    quadraticNeumannFirstIndexDistinctContribution Omega S 0 = 0 := by
  unfold quadraticNeumannFirstIndexDistinctContribution; simp
theorem middle_p0 (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) :
    quadraticNeumannMiddleIndexDistinctContribution Omega S 0 = 0 := by
  unfold quadraticNeumannMiddleIndexDistinctContribution; simp
theorem last_p0 (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) :
    quadraticNeumannLastIndexDistinctContribution Omega S 0 = 0 := by
  unfold quadraticNeumannLastIndexDistinctContribution; simp
theorem allDistinct_p0 (S : SVD M r) (Omega : Finset (Fin n1 × Fin n2)) :
    quadraticNeumannAllDistinctContribution Omega S 0 = 0 := by
  unfold quadraticNeumannAllDistinctContribution; simp

theorem normalProjection_zero' (S : SVD M r) :
    normalProjection S (0 : RealMatrix n1 n2) = 0 := by
  unfold normalProjection
  rw [show tangentProjection S (0 : RealMatrix n1 n2) = 0 from by
    funext i j; unfold tangentProjection leftSingularProjection rightSingularProjection twoSidedSingularProjection
    simp [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply]]
  abel


end MatrixCompletion

open MatrixCompletion

/-- PROOF: neumannCertificateTerm 2 = normalProjection of the 5-class quadratic correction
(CR §6.3 eq (6.20)).  Reduction: cert₂ = normalProjection(cSF(H²(E))); the 5 contributions
exactly partition the triple sum Σ_{ω1,ω2,ω3} ξξξ E K(ω3,ω2)K(ω2,ω1) e_{ω1} = cSF(H²(E)).
Unlike the k=1 case, the two H-applications give (-p⁻¹)² = +p⁻², so the sign is +. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ) :
    neumannCertificateTerm Omega S p 2 =
      normalProjection S
        ((((quadraticNeumannAllEqualContribution Omega S p +
          quadraticNeumannFirstIndexDistinctContribution Omega S p) +
          quadraticNeumannMiddleIndexDistinctContribution Omega S p) +
          quadraticNeumannLastIndexDistinctContribution Omega S p) +
          quadraticNeumannAllDistinctContribution Omega S p) := by
  by_cases hp : p = 0
  · subst hp
    rw [certTerm2_p0, allEqual_p0, first_p0, middle_p0, last_p0, allDistinct_p0]
    rw [add_zero, add_zero, add_zero, add_zero, normalProjection_zero']
  · rw [certTerm2_eq_normalProj_cSF S Omega p hp]
    rw [← sum5_eq_cSF_Y2 S Omega p hp]

#print axioms solution
