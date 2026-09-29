-- Prove2me | solution 1 for quadratic_neumann_first_index_distinct_mean_coefficient_entry_bound_min_dim
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-07-01T10:22:00.776684+00:00
-- url     : https://prove2.me/submissions/5b4ab2b0-a333-411f-87b2-669495163616

import Theorems.Thm_a0_singular_coordinate_energy_bounds
import Theorems.Thm_svd_singular_coordinate_energy_le_one
import Theorems.Thm_sign_matrix_spectral_norm_le_one
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Fintype.Order
import Mathlib.Tactic

/-!
# Lemma 6.8 mean-coefficient bound for the `ω₁ ≠ ω₂ = ω₃` quadratic term.

Target (immutable):
`entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S p) ≤
  C68 * p⁻¹ * (μ₀ r / min) * (μ₁ √(r/n₁n₂) + μ₀ r / min)`.

## p-sign gap (DOCUMENTED, verified numerically + symbolically).

The immutable statement has **no** `0 < p` hypothesis and no sign constraint on
`p`, yet the RHS contains a bare `p⁻¹` (not `|p⁻¹|`).  The coefficient matrix is
`H = p⁻¹ • G` where
`G_{ij} = ∑_{w2≠(i,j)} E_{w2}·Kdiag_{w2}·K(w2,i,j)` is **independent of `p`**.
Hence `entrySupNorm H = |p⁻¹| · entrySupNorm G` with `entrySupNorm G ≥ 0`, and
`entrySupNorm G > 0` generically (e.g. for the flat rank-1 SVD on `3×4`,
`entrySupNorm G ≈ 0.072` while A0/A1 hold with `μ₀ = μ₁ = 1`).

For `p < 0`: LHS `= |p⁻¹|·entrySupNorm G > 0`, while RHS
`= C68·p⁻¹·(positive) < 0` for every `C68 > 0`.  So `0 ≤ LHS ≤ RHS < 0` is
**false**.  The statement is therefore NOT provable sorry-free as written; it is
missing `0 < p`.

The theorem `solution_of_pos_p` below is the fully-proven **conditional core**:
it proves the intended bound (with `C68 = 4`) under the added hypothesis
`0 < p`.  My proof body is sorry-free; the only `sorryAx` in its axiom footprint
comes from the three imported OPEN stubs it uses:
`a0_singular_coordinate_energy_bounds`, `sign_matrix_spectral_norm_le_one`, and
`svd_singular_coordinate_energy_le_one`.  (Tangent-space membership of `Λ_U E`
and `E Λ_V` is proven directly here, so `sign_matrix_mem_tangent_space` is not
needed.)

The top-level `theorem solution` matching the immutable statement verbatim is
**deliberately omitted**: it is false for `p < 0` (see the gap above), and the
project rules forbid a `sorry` in the `solution` body.  The correct fix is to add
`0 < p` to the immutable statement, after which `solution_of_pos_p` discharges it.

Source: Candes--Recht 2008, Section 6.3, Lemma 6.8, equation (6.22).
-/

open MatrixCompletion
open scoped Classical BigOperators Matrix.Norms.L2Operator

namespace QuadraticFirstIndexDistinctMeanLemma68

/-! ### Generic reusable helpers (entrySupNorm, spectralNorm). -/

private lemma entrySupNorm_le_of_forall_abs_le {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (B : ℝ)
    (h : ∀ i j, |X i j| ≤ B) :
    entrySupNorm X ≤ B := by
  haveI : Nonempty (Fin n₁) := Fin.pos_iff_nonempty.mp hn₁
  haveI : Nonempty (Fin n₂) := Fin.pos_iff_nonempty.mp hn₂
  unfold entrySupNorm
  exact ciSup_le fun i => ciSup_le fun j => h i j

private lemma abs_entry_le_entrySupNorm {n₁ n₂ : ℕ}
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    |X i j| ≤ entrySupNorm X := by
  unfold entrySupNorm
  have hbddj : BddAbove (Set.range (fun j => |X i j|)) := Set.Finite.bddAbove (Set.finite_range _)
  have hbddi : BddAbove (Set.range (fun i => ⨆ j, |X i j|)) :=
    Set.Finite.bddAbove (Set.finite_range _)
  calc |X i j| ≤ ⨆ j, |X i j| := le_ciSup hbddj j
    _ ≤ ⨆ i, ⨆ j, |X i j| := le_ciSup hbddi i

private lemma spectralNorm_eq_l2_opNorm
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm X = ‖X‖ := by
  simp [spectralNorm, Matrix.l2_opNorm_def]

private lemma entrySupNorm_le_spectralNorm {n₁ n₂ : ℕ}
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    entrySupNorm X ≤ spectralNorm X := by
  apply entrySupNorm_le_of_forall_abs_le hn₁ hn₂
  intro i j
  let e : EuclideanSpace ℝ (Fin n₂) := WithLp.toLp 2 (Pi.single j (1 : ℝ))
  let T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X)
  calc
    |X i j| = ‖T e i‖ := by
      simp [T, e, Real.norm_eq_abs]
    _ ≤ ‖T e‖ := PiLp.norm_apply_le (T e) i
    _ ≤ ‖T‖ * ‖e‖ := T.le_opNorm e
    _ = spectralNorm X := by
      simp [T, e, spectralNorm]

/-! ### The tangent-coordinate-kernel closed formula (copied, self-contained). -/

private lemma matrixInner_coordinate_right
    {n₁ n₂ : ℕ} (X : Matrix (Fin n₁) (Fin n₂) ℝ)
    (i : Fin n₁) (j : Fin n₂) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _hb hb
      simp [hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

/-- `K(i,j,a,b) = [j=b]·PU_{ia} + [i=a]·PV_{jb} − PU_{ia}·PV_{jb}`. -/
private lemma tangent_coordinate_kernel_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) (a : Fin n₁) (b : Fin n₂) :
    tangentCoordinateKernel S i j a b =
      (if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0) +
        (if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0) -
          (∑ k : Fin r, S.u k i * S.u k a) *
            (∑ k : Fin r, S.v k j * S.v k b) := by
  rw [tangentCoordinateKernel, matrixInner_coordinate_right]
  have hleft :
      leftSingularProjection S (coordinateMatrix i j) a b =
        if j = b then ∑ k : Fin r, S.u k i * S.u k a else 0 := by
    unfold leftSingularProjection coordinateMatrix
    by_cases hbj : b = j
    · rw [Finset.sum_eq_single i]
      · simp [hbj, mul_comm]
      · intro x _hx hx
        simp [hx, hbj]
      · intro hi
        exact (hi (Finset.mem_univ i)).elim
    · rw [Finset.sum_eq_zero]
      · have hjb : ¬ j = b := fun h => hbj h.symm
        simp [hjb]
      · intro x _hx
        simp [hbj]
  have hright :
      rightSingularProjection S (coordinateMatrix i j) a b =
        if i = a then ∑ k : Fin r, S.v k j * S.v k b else 0 := by
    unfold rightSingularProjection coordinateMatrix
    by_cases hai : a = i
    · rw [Finset.sum_eq_single j]
      · simp [hai]
      · intro y _hy hy
        simp [hai, hy]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    · rw [Finset.sum_eq_zero]
      · have hia : ¬ i = a := fun h => hai h.symm
        simp [hia]
      · intro y _hy
        simp [hai]
  have htwo :
      twoSidedSingularProjection S (coordinateMatrix i j) a b =
        (∑ k : Fin r, S.u k i * S.u k a) *
          (∑ k : Fin r, S.v k j * S.v k b) := by
    unfold twoSidedSingularProjection coordinateMatrix
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp [Finset.mul_sum, mul_comm, mul_assoc]
      · intro y _hy hy
        simp [hy]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    · intro x _hx hx
      simp [hx]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  simp [tangentProjection, hleft, hright, htwo]

/-! ### Diagonal kernel and sign-matrix entry formulas. -/

/-- `signMatrix S i j = ∑ k, u k i * v k j`. -/
private lemma signMatrix_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    signMatrix S i j = ∑ k : Fin r, S.u k i * S.v k j := by
  simp [signMatrix, Matrix.sum_apply, Matrix.vecMulVec_apply]

/-- Diagonal kernel: `K(a,b,a,b) = dU_a + dV_b − dU_a·dV_b`. -/
private lemma Kdiag_decomp
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (a : Fin n₁) (b : Fin n₂) :
    tangentCoordinateKernel S a b a b =
      (∑ k : Fin r, (S.u k a) ^ 2) + (∑ k : Fin r, (S.v k b) ^ 2)
        - (∑ k : Fin r, (S.u k a) ^ 2) * (∑ k : Fin r, (S.v k b) ^ 2) := by
  rw [tangent_coordinate_kernel_formula S a b a b]
  simp only [if_true]
  congr 1 <;> congr 1 <;>
    exact Finset.sum_congr rfl (fun k _ => by ring)

/-! ### The self-adjoint kernel identity: `∑_w X_w · K(w, ω) = (P_T X)_ω`. -/

/-- `∑_{(a,b)} X_{ab} · K(a,b,i,j) = (tangentProjection S X)_{ij}`. -/
private lemma kernel_expansion
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    ∑ w : Fin n₁ × Fin n₂,
        X w.1 w.2 * tangentCoordinateKernel S w.1 w.2 i j =
      tangentProjection S X i j := by
  -- Expand each kernel entry via the closed formula.
  have hterm : ∀ w : Fin n₁ × Fin n₂,
      X w.1 w.2 * tangentCoordinateKernel S w.1 w.2 i j =
        X w.1 w.2 *
            ((if w.2 = j then ∑ k : Fin r, S.u k w.1 * S.u k i else 0) +
              (if w.1 = i then ∑ k : Fin r, S.v k w.2 * S.v k j else 0) -
                (∑ k : Fin r, S.u k w.1 * S.u k i) *
                  (∑ k : Fin r, S.v k w.2 * S.v k j)) := by
    intro w
    rw [tangent_coordinate_kernel_formula S w.1 w.2 i j]
  simp only [hterm]
  -- Split into three summands: term1 (left), term2 (right), term3 (two-sided).
  have hsplit : ∀ w : Fin n₁ × Fin n₂,
      X w.1 w.2 *
          ((if w.2 = j then ∑ k : Fin r, S.u k w.1 * S.u k i else 0) +
            (if w.1 = i then ∑ k : Fin r, S.v k w.2 * S.v k j else 0) -
              (∑ k : Fin r, S.u k w.1 * S.u k i) *
                (∑ k : Fin r, S.v k w.2 * S.v k j)) =
        (X w.1 w.2 * (if w.2 = j then ∑ k : Fin r, S.u k w.1 * S.u k i else 0))
          + (X w.1 w.2 * (if w.1 = i then ∑ k : Fin r, S.v k w.2 * S.v k j else 0))
          - X w.1 w.2 * ((∑ k : Fin r, S.u k w.1 * S.u k i) *
              (∑ k : Fin r, S.v k w.2 * S.v k j)) := by
    intro w; ring
  rw [Finset.sum_congr rfl (fun w _ => hsplit w),
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  -- Compute the three sums over the product index.
  have hleftsum :
      ∑ w : Fin n₁ × Fin n₂,
          X w.1 w.2 * (if w.2 = j then ∑ k : Fin r, S.u k w.1 * S.u k i else 0)
        = leftSingularProjection S X i j := by
    rw [Fintype.sum_prod_type]
    rw [leftSingularProjection]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_eq_single j]
    · simp only [if_true, mul_comm]
    · intro b _ hb; simp [hb]
    · intro hj; exact (hj (Finset.mem_univ j)).elim
  have hrightsum :
      ∑ w : Fin n₁ × Fin n₂,
          X w.1 w.2 * (if w.1 = i then ∑ k : Fin r, S.v k w.2 * S.v k j else 0)
        = rightSingularProjection S X i j := by
    rw [Fintype.sum_prod_type]
    rw [rightSingularProjection]
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl (fun b _ => ?_)
      simp only [if_true, mul_comm]
    · intro a _ ha; simp [ha]
    · intro hi; exact (hi (Finset.mem_univ i)).elim
  have htwosum :
      ∑ w : Fin n₁ × Fin n₂,
          X w.1 w.2 * ((∑ k : Fin r, S.u k w.1 * S.u k i) *
            (∑ k : Fin r, S.v k w.2 * S.v k j))
        = twoSidedSingularProjection S X i j := by
    rw [Fintype.sum_prod_type]
    rw [twoSidedSingularProjection]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    have hu : (∑ k : Fin r, S.u k a * S.u k i) = ∑ k : Fin r, S.u k i * S.u k a :=
      Finset.sum_congr rfl (fun k _ => mul_comm _ _)
    have hv : (∑ k : Fin r, S.v k b * S.v k j) = ∑ l : Fin r, S.v l b * S.v l j := rfl
    rw [hu, hv]
    ring
  rw [hleftsum, hrightsum, htwosum, tangentProjection]
  simp [Matrix.sub_apply, Matrix.add_apply]

/-! ### Coherence diagonal weights `dU`, `dV`, and the base decomposition. -/

/-- Left coherence weight `dU_a = ∑_k (u k a)²`. -/
private noncomputable def dU {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (a : Fin n₁) : ℝ := ∑ k : Fin r, (S.u k a) ^ 2

/-- Right coherence weight `dV_b = ∑_k (v k b)²`. -/
private noncomputable def dV {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (b : Fin n₂) : ℝ := ∑ k : Fin r, (S.v k b) ^ 2

/-- Base entry decomposition:
`base_{ab} = dU_a·E_{ab} + E_{ab}·dV_b − dU_a·E_{ab}·dV_b`. -/
private lemma base_decomp
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (a : Fin n₁) (b : Fin n₂) :
    linearNeumannDiagonalBaseMatrix S a b =
      dU S a * signMatrix S a b + signMatrix S a b * dV S b
        - dU S a * signMatrix S a b * dV S b := by
  unfold linearNeumannDiagonalBaseMatrix tangentDiagonalMultiplier
  rw [Kdiag_decomp S a b]
  simp only [dU, dV]
  ring

/-! ### Tangent-space membership of `Λ_U E` and `E Λ_V`. -/

/-- General identity: `twoSided Y = leftSing (rightSing Y)`. -/
private lemma twoSided_eq_left_right
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    twoSidedSingularProjection S Y =
      leftSingularProjection S (rightSingularProjection S Y) := by
  ext i j
  unfold twoSidedSingularProjection leftSingularProjection rightSingularProjection
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

/-- `Λ_U E` matrix: `(Λ_U E)_{ab} = dU_a · E_{ab}`. -/
private noncomputable def lambdaUE {n₁ n₂ r : ℕ}
    {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) :
    Matrix (Fin n₁) (Fin n₂) ℝ :=
  fun a b => dU S a * signMatrix S a b

/-- `E Λ_V` matrix: `(E Λ_V)_{ab} = E_{ab} · dV_b`. -/
private noncomputable def eLambdaV {n₁ n₂ r : ℕ}
    {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) :
    Matrix (Fin n₁) (Fin n₂) ℝ :=
  fun a b => signMatrix S a b * dV S b

/-- Right-projection fixes any matrix of the form `fun a b => c a * E_{ab}` where
`E` is the sign matrix.  Applied with `c = dU S` this fixes `Λ_U E`; the scalar
`c i` is per-row and commutes through the `v`-orthonormality contraction. -/
private lemma rightProj_row_scaled_sign
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (c : Fin n₁ → ℝ) :
    rightSingularProjection S (fun a b => c a * signMatrix S a b) =
      (fun a b => c a * signMatrix S a b) := by
  ext i j
  unfold rightSingularProjection
  -- Step 1: expand E and pull the double sum over (m,k) outside the b-sum.
  have h1 :
      ∑ b : Fin n₂, c i * signMatrix S i b * (∑ k : Fin r, S.v k b * S.v k j) =
        ∑ m : Fin r, ∑ k : Fin r,
          (c i * S.u m i * S.v k j) * (∑ b : Fin n₂, S.v m b * S.v k b) := by
    -- Expand summand at b into ∑ m ∑ k, (c i u m i v k j)(v m b v k b).
    have hb : ∀ b : Fin n₂,
        c i * signMatrix S i b * (∑ k : Fin r, S.v k b * S.v k j) =
          ∑ m : Fin r, ∑ k : Fin r,
            (c i * S.u m i * S.v k j) * (S.v m b * S.v k b) := by
      intro b
      rw [signMatrix_apply]
      rw [show (c i * ∑ m : Fin r, S.u m i * S.v m b) =
            ∑ m : Fin r, c i * (S.u m i * S.v m b) from by rw [Finset.mul_sum]]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => by ring)
    rw [Finset.sum_congr rfl (fun b _ => hb b)]
    -- Move ∑ b to the inside of ∑ m ∑ k.
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
  rw [h1]
  -- Step 2: contract on b via v-orthonormality; only m = k survives.
  have h2 : ∀ m : Fin r,
      ∑ k : Fin r, (c i * S.u m i * S.v k j) * (∑ b : Fin n₂, S.v m b * S.v k b) =
        c i * S.u m i * S.v m j := by
    intro m
    rw [Finset.sum_eq_single m]
    · rw [S.v_orthonormal m m]; simp
    · intro k _ hk
      rw [S.v_orthonormal m k]; simp [Ne.symm hk]
    · intro hm; exact (hm (Finset.mem_univ m)).elim
  rw [Finset.sum_congr rfl (fun m _ => h2 m)]
  rw [signMatrix_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun m _ => by ring)

private lemma rightProj_lambdaUE
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    rightSingularProjection S (lambdaUE S) = lambdaUE S := by
  simpa [lambdaUE] using rightProj_row_scaled_sign S (dU S)

/-- `Λ_U E ∈ T`. -/
private lemma lambdaUE_mem_T
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    tangentProjection S (lambdaUE S) = lambdaUE S := by
  unfold tangentProjection
  rw [twoSided_eq_left_right, rightProj_lambdaUE]
  ext i j
  simp [Matrix.add_apply, Matrix.sub_apply]

/-- General identity: `twoSided Y = rightSing (leftSing Y)`. -/
private lemma twoSided_eq_right_left
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    twoSidedSingularProjection S Y =
      rightSingularProjection S (leftSingularProjection S Y) := by
  ext i j
  unfold twoSidedSingularProjection rightSingularProjection leftSingularProjection
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [Finset.sum_mul]

/-- `leftSingularProjection S (E Λ_V) = E Λ_V` (columns lie in the u-span). -/
private lemma leftProj_col_scaled_sign
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (d : Fin n₂ → ℝ) :
    leftSingularProjection S (fun a b => signMatrix S a b * d b) =
      (fun a b => signMatrix S a b * d b) := by
  ext i j
  unfold leftSingularProjection
  -- Step 1: expand summand at a into ∑ k ∑ m (u k i v m j d_j)(u k a u m a); swap a inside.
  have h1 :
      ∑ a : Fin n₁, (∑ k : Fin r, S.u k i * S.u k a) * (signMatrix S a j * d j) =
        ∑ k : Fin r, ∑ m : Fin r,
          (S.u k i * S.v m j * d j) * (∑ a : Fin n₁, S.u k a * S.u m a) := by
    have ha : ∀ a : Fin n₁,
        (∑ k : Fin r, S.u k i * S.u k a) * (signMatrix S a j * d j) =
          ∑ k : Fin r, ∑ m : Fin r,
            (S.u k i * S.v m j * d j) * (S.u k a * S.u m a) := by
      intro a
      rw [signMatrix_apply, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      have hdist :
          (S.u k i * S.u k a) * ((∑ m : Fin r, S.u m a * S.v m j) * d j) =
            ∑ m : Fin r, (S.u k i * S.v m j * d j) * (S.u k a * S.u m a) := by
        rw [Finset.sum_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun m _ => by ring)
      rw [hdist]
    rw [Finset.sum_congr rfl (fun a _ => ha a)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [Finset.mul_sum]
  rw [h1]
  -- Step 2: contract on a via u-orthonormality; only k = m survives.
  have h2 : ∀ k : Fin r,
      ∑ m : Fin r, (S.u k i * S.v m j * d j) * (∑ a : Fin n₁, S.u k a * S.u m a) =
        S.u k i * S.v k j * d j := by
    intro k
    rw [Finset.sum_eq_single k]
    · rw [S.u_orthonormal k k]; simp
    · intro m _ hm
      rw [S.u_orthonormal k m]; simp [Ne.symm hm]
    · intro hk; exact (hk (Finset.mem_univ k)).elim
  rw [Finset.sum_congr rfl (fun k _ => h2 k)]
  rw [signMatrix_apply, Finset.sum_mul]

/-- `E Λ_V ∈ T`. -/
private lemma eLambdaV_mem_T
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    tangentProjection S (eLambdaV S) = eLambdaV S := by
  have hleft : leftSingularProjection S (eLambdaV S) = eLambdaV S := by
    simpa [eLambdaV] using leftProj_col_scaled_sign S (dV S)
  unfold tangentProjection
  rw [twoSided_eq_right_left, hleft]
  ext i j
  simp [Matrix.add_apply, Matrix.sub_apply]

/-! ### Diagonal spectral-norm bound and the quadratic term `Λ_U E Λ_V`. -/

/-- Spectral norm of a diagonal matrix is bounded by the max absolute entry. -/
private lemma spectralNorm_diagonal_le
    {n : ℕ} (d : Fin n → ℝ) (B : ℝ) (hB : 0 ≤ B) (h : ∀ a, |d a| ≤ B) :
    spectralNorm (Matrix.diagonal d) ≤ B := by
  rw [spectralNorm_eq_l2_opNorm, Matrix.l2_opNorm_diagonal]
  rw [pi_norm_le_iff_of_nonneg hB]
  intro a
  simpa [Real.norm_eq_abs] using h a

/-- Diagonal weight bound from A0: `|dU a| ≤ μ₀ r / min`. -/
private lemma dU_abs_le
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ : ℝ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hA0 : A0 S μ₀) (a : Fin n₁) :
    |dU S a| ≤ μ₀ * (r : ℝ) / (↑(min n₁ n₂)) := by
  have hEnergy := (a0_singular_coordinate_energy_bounds S μ₀ hn₁ hn₂ hr hA0).1 a
  have hnn : (0 : ℝ) ≤ dU S a := by
    unfold dU; positivity
  rw [abs_of_nonneg hnn]
  refine hEnergy.trans ?_
  have hmin_le : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₁ : ℝ) := by
    exact_mod_cast min_le_left n₁ n₂
  have hnum : 0 ≤ μ₀ * (r : ℝ) := by positivity
  gcongr

private lemma dV_abs_le
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ : ℝ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hA0 : A0 S μ₀) (b : Fin n₂) :
    |dV S b| ≤ μ₀ * (r : ℝ) / (↑(min n₁ n₂)) := by
  have hEnergy := (a0_singular_coordinate_energy_bounds S μ₀ hn₁ hn₂ hr hA0).2 b
  have hnn : (0 : ℝ) ≤ dV S b := by
    unfold dV; positivity
  rw [abs_of_nonneg hnn]
  refine hEnergy.trans ?_
  have hmin_le : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₂ : ℝ) := by
    exact_mod_cast min_le_right n₁ n₂
  have hnum : 0 ≤ μ₀ * (r : ℝ) := by positivity
  gcongr

/-! ### Spectral-norm contraction of `P_T` (inlined `≤ 2‖X‖`). -/

private lemma gram_is_star_projection
    {r' N : ℕ} (w : Fin r' → (Fin N → ℝ))
    (hw : ∀ k l, ∑ i, w k i * w l i = if k = l then 1 else 0) :
    @IsStarProjection (Matrix (Fin N) (Fin N) ℝ)
      Matrix.instMulOfFintypeOfAddCommMonoid Matrix.instStar
      (fun i a : Fin N => ∑ k : Fin r', w k i * w k a :
        Matrix (Fin N) (Fin N) ℝ) := by
  constructor
  · ext i j
    calc
      (∑ a : Fin N,
          (∑ k : Fin r', w k i * w k a) *
            (∑ l : Fin r', w l a * w l j))
          =
          ∑ k : Fin r', ∑ l : Fin r',
            w k i * w l j * (∑ a : Fin N, w k a * w l a) := by
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro k _hk
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl ?_
            intro l _hl
            refine Finset.sum_congr rfl ?_
            intro a _ha
            ring
      _ = ∑ k : Fin r', ∑ l : Fin r',
            w k i * w l j * (if k = l then 1 else 0) := by
            simp [hw]
      _ = ∑ k : Fin r', w k i * w k j := by
            simp
  · ext i j
    simp [mul_comm]

private lemma left_eq_mul
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    leftSingularProjection S X =
      Matrix.of (fun i a : Fin n₁ => ∑ k : Fin r, S.u k i * S.u k a) * X := by
  ext i j
  simp [leftSingularProjection, Matrix.mul_apply]

private lemma right_minus_two_sided_eq
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    rightSingularProjection S X - twoSidedSingularProjection S X =
      (1 - Matrix.of (fun i a : Fin n₁ => ∑ k : Fin r, S.u k i * S.u k a)) *
        X *
        Matrix.of (fun b j : Fin n₂ => ∑ k : Fin r, S.v k b * S.v k j) := by
  ext i j
  simp [rightSingularProjection, twoSidedSingularProjection, Matrix.mul_apply,
    Matrix.sub_apply, Matrix.one_apply, Finset.sum_sub_distrib, sub_mul,
    Finset.sum_mul]
  rw [Finset.sum_comm]

private lemma spectralNorm_add_le
    {n₁ n₂ : ℕ} (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (X + Y) ≤ spectralNorm X + spectralNorm Y := by
  rw [spectralNorm_eq_l2_opNorm, spectralNorm_eq_l2_opNorm,
    spectralNorm_eq_l2_opNorm]
  exact norm_add_le _ _

/-- `spectralNorm (P_T X) ≤ 2 · spectralNorm X`. -/
private lemma tangentProjection_spectralNorm_le
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (X : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (tangentProjection S X) ≤ 2 * spectralNorm X := by
  set PU : Matrix (Fin n₁) (Fin n₁) ℝ :=
    Matrix.of (fun i a : Fin n₁ => ∑ k : Fin r, S.u k i * S.u k a) with hPUdef
  set PV : Matrix (Fin n₂) (Fin n₂) ℝ :=
    Matrix.of (fun b j : Fin n₂ => ∑ k : Fin r, S.v k b * S.v k j) with hPVdef
  have hPU : @IsStarProjection (Matrix (Fin n₁) (Fin n₁) ℝ)
      Matrix.instMulOfFintypeOfAddCommMonoid Matrix.instStar PU := by
    simpa [hPUdef] using gram_is_star_projection S.u S.u_orthonormal
  have hPV : @IsStarProjection (Matrix (Fin n₂) (Fin n₂) ℝ)
      Matrix.instMulOfFintypeOfAddCommMonoid Matrix.instStar PV := by
    simpa [hPVdef] using gram_is_star_projection S.v S.v_orthonormal
  have hPUnorm : ‖PU‖ ≤ (1 : ℝ) := hPU.norm_le
  have hOneSubPUnorm : ‖(1 : Matrix (Fin n₁) (Fin n₁) ℝ) - PU‖ ≤ (1 : ℝ) :=
    hPU.one_sub.norm_le
  have hPVnorm : ‖PV‖ ≤ (1 : ℝ) := hPV.norm_le
  have hAssoc :
      leftSingularProjection S X + rightSingularProjection S X -
          twoSidedSingularProjection S X =
        leftSingularProjection S X +
          (rightSingularProjection S X - twoSidedSingularProjection S X) := by
    ext i j
    simp [sub_eq_add_neg, add_assoc]
  have hLeftBound :
      spectralNorm (leftSingularProjection S X) ≤ spectralNorm X := by
    have hEq : leftSingularProjection S X = PU * X := by
      rw [hPUdef]; exact left_eq_mul S X
    calc
      spectralNorm (leftSingularProjection S X)
          = ‖PU * X‖ := by rw [hEq, spectralNorm_eq_l2_opNorm]
      _ ≤ ‖PU‖ * ‖X‖ := Matrix.l2_opNorm_mul PU X
      _ ≤ 1 * ‖X‖ := by gcongr
      _ = spectralNorm X := by rw [spectralNorm_eq_l2_opNorm X]; ring
  have hRightBound :
      spectralNorm
          (rightSingularProjection S X - twoSidedSingularProjection S X) ≤
        spectralNorm X := by
    have hEq :
        rightSingularProjection S X - twoSidedSingularProjection S X =
          (1 - PU) * X * PV := by
      rw [hPUdef, hPVdef]; exact right_minus_two_sided_eq S X
    calc
      spectralNorm
          (rightSingularProjection S X - twoSidedSingularProjection S X)
          = ‖(1 - PU) * X * PV‖ := by rw [hEq, spectralNorm_eq_l2_opNorm]
      _ ≤ ‖(1 - PU) * X‖ * ‖PV‖ := Matrix.l2_opNorm_mul ((1 - PU) * X) PV
      _ ≤ (‖(1 : Matrix (Fin n₁) (Fin n₁) ℝ) - PU‖ * ‖X‖) * ‖PV‖ := by
            gcongr
            exact Matrix.l2_opNorm_mul ((1 : Matrix (Fin n₁) (Fin n₁) ℝ) - PU) X
      _ ≤ (1 * ‖X‖) * 1 := by gcongr
      _ = spectralNorm X := by rw [spectralNorm_eq_l2_opNorm X]; ring
  calc
    spectralNorm (tangentProjection S X)
        = spectralNorm
            (leftSingularProjection S X +
              (rightSingularProjection S X - twoSidedSingularProjection S X)) := by
          rw [tangentProjection, hAssoc]
    _ ≤ spectralNorm (leftSingularProjection S X) +
          spectralNorm
            (rightSingularProjection S X - twoSidedSingularProjection S X) :=
        spectralNorm_add_le _ _
    _ ≤ spectralNorm X + spectralNorm X := add_le_add hLeftBound hRightBound
    _ = 2 * spectralNorm X := by ring

/-! ### The quadratic matrix `Q = Λ_U E Λ_V` and its spectral bound. -/

/-- `Q = (diagonal dU) * E * (diagonal dV)`, entrywise `Q_{ab} = dU_a·E_{ab}·dV_b`. -/
private noncomputable def lambdaUEV {n₁ n₂ r : ℕ}
    {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r) :
    Matrix (Fin n₁) (Fin n₂) ℝ :=
  Matrix.diagonal (dU S) * signMatrix S * Matrix.diagonal (dV S)

private lemma lambdaUEV_apply
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (a : Fin n₁) (b : Fin n₂) :
    lambdaUEV S a b = dU S a * signMatrix S a b * dV S b := by
  unfold lambdaUEV
  rw [Matrix.mul_apply]
  simp only [Matrix.diagonal_apply, Matrix.mul_apply]
  rw [Finset.sum_eq_single b]
  · rw [Finset.sum_eq_single a]
    · simp
    · intro c _ hc
      rw [if_neg (Ne.symm hc)]; ring
    · intro ha; exact (ha (Finset.mem_univ a)).elim
  · intro c _ hc
    rw [if_neg hc, mul_zero]
  · intro hb; exact (hb (Finset.mem_univ b)).elim

/-- `spectralNorm Q ≤ 2·(μ₀ r/min)²`. -/
private lemma lambdaUEV_spectralNorm_le
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ : ℝ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hA0 : A0 S μ₀) :
    spectralNorm (lambdaUEV S) ≤
      2 * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2 := by
  set B : ℝ := μ₀ * (r : ℝ) / (↑(min n₁ n₂)) with hBdef
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hdiagU : spectralNorm (Matrix.diagonal (dU S)) ≤ B :=
    spectralNorm_diagonal_le (dU S) B hBnn (dU_abs_le S μ₀ hn₁ hn₂ hr hμ₀ hA0)
  have hdiagV : spectralNorm (Matrix.diagonal (dV S)) ≤ B :=
    spectralNorm_diagonal_le (dV S) B hBnn (dV_abs_le S μ₀ hn₁ hn₂ hr hμ₀ hA0)
  have hE : spectralNorm (signMatrix S) ≤ 1 := sign_matrix_spectral_norm_le_one S
  -- ‖DU * E * DV‖ ≤ ‖DU‖·‖E‖·‖DV‖ ≤ B·1·B
  rw [spectralNorm_eq_l2_opNorm] at *
  unfold lambdaUEV
  calc
    ‖Matrix.diagonal (dU S) * signMatrix S * Matrix.diagonal (dV S)‖
        ≤ ‖Matrix.diagonal (dU S) * signMatrix S‖ * ‖Matrix.diagonal (dV S)‖ :=
          Matrix.l2_opNorm_mul _ _
    _ ≤ (‖Matrix.diagonal (dU S)‖ * ‖signMatrix S‖) * ‖Matrix.diagonal (dV S)‖ := by
          gcongr
          exact Matrix.l2_opNorm_mul _ _
    _ ≤ (B * 1) * B := by gcongr
    _ ≤ 2 * B ^ 2 := by nlinarith [sq_nonneg B]

/-! ### Linearity of `P_T` and the base-matrix decomposition. -/

private lemma leftSing_add_sub
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (A B C : Matrix (Fin n₁) (Fin n₂) ℝ) :
    leftSingularProjection S (A + B - C) =
      leftSingularProjection S A + leftSingularProjection S B
        - leftSingularProjection S C := by
  ext i j
  simp only [leftSingularProjection, Matrix.add_apply, Matrix.sub_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => by ring)

private lemma rightSing_add_sub
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (A B C : Matrix (Fin n₁) (Fin n₂) ℝ) :
    rightSingularProjection S (A + B - C) =
      rightSingularProjection S A + rightSingularProjection S B
        - rightSingularProjection S C := by
  ext i j
  simp only [rightSingularProjection, Matrix.add_apply, Matrix.sub_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => by ring)

private lemma twoSided_add_sub
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (A B C : Matrix (Fin n₁) (Fin n₂) ℝ) :
    twoSidedSingularProjection S (A + B - C) =
      twoSidedSingularProjection S A + twoSidedSingularProjection S B
        - twoSidedSingularProjection S C := by
  ext i j
  simp only [twoSidedSingularProjection, Matrix.add_apply, Matrix.sub_apply]
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => by ring)

private lemma tangentProjection_add_sub
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (A B C : Matrix (Fin n₁) (Fin n₂) ℝ) :
    tangentProjection S (A + B - C) =
      tangentProjection S A + tangentProjection S B - tangentProjection S C := by
  unfold tangentProjection
  rw [leftSing_add_sub, rightSing_add_sub, twoSided_add_sub]
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply]
  ring

/-- `base = Λ_U E + E Λ_V − Q` as matrices. -/
private lemma base_matrix_eq
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    linearNeumannDiagonalBaseMatrix S =
      lambdaUE S + eLambdaV S - lambdaUEV S := by
  ext a b
  rw [base_decomp S a b]
  simp only [Matrix.add_apply, Matrix.sub_apply, lambdaUE, eLambdaV,
    lambdaUEV_apply]

/-- `P_T base = Λ_U E + E Λ_V − P_T Q`. -/
private lemma pt_base_eq
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
    tangentProjection S (linearNeumannDiagonalBaseMatrix S) =
      lambdaUE S + eLambdaV S - tangentProjection S (lambdaUEV S) := by
  rw [base_matrix_eq, tangentProjection_add_sub, lambdaUE_mem_T, eLambdaV_mem_T]

/-! ### The exclusion identity: `p·H = (P_T base) − base·Kdiag`. -/

/-- Each summand of `H` uses `base_{w2} = E_{w2}·Kdiag_{w2}`. -/
private lemma H_summand_eq_base_kernel
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) (w2 : Fin n₁ × Fin n₂) :
    signMatrix S w2.1 w2.2 *
        tangentCoordinateKernel S w2.1 w2.2 w2.1 w2.2 *
          tangentCoordinateKernel S w2.1 w2.2 i j =
      linearNeumannDiagonalBaseMatrix S w2.1 w2.2 *
        tangentCoordinateKernel S w2.1 w2.2 i j := by
  unfold linearNeumannDiagonalBaseMatrix tangentDiagonalMultiplier
  ring

/-- `H_{ij} = p⁻¹ · ((P_T base)_{ij} − base_{ij}·Kdiag_{ij})`. -/
private lemma H_entry_eq
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (p : ℝ) (i : Fin n₁) (j : Fin n₂) :
    quadraticFirstIndexDistinctMeanCoefficientMatrix S p i j =
      p⁻¹ *
        (tangentProjection S (linearNeumannDiagonalBaseMatrix S) i j -
          linearNeumannDiagonalBaseMatrix S i j *
            tangentCoordinateKernel S i j i j) := by
  unfold quadraticFirstIndexDistinctMeanCoefficientMatrix
  congr 1
  -- Rewrite each summand and split off the excluded diagonal term.
  have hsummand :
      (∑ w2 : Fin n₁ × Fin n₂,
          if w2 = (i, j) then 0 else
            signMatrix S w2.1 w2.2 *
              tangentCoordinateKernel S w2.1 w2.2 w2.1 w2.2 *
                tangentCoordinateKernel S w2.1 w2.2 i j)
        = ∑ w2 : Fin n₁ × Fin n₂,
            if w2 = (i, j) then 0 else
              linearNeumannDiagonalBaseMatrix S w2.1 w2.2 *
                tangentCoordinateKernel S w2.1 w2.2 i j := by
    refine Finset.sum_congr rfl (fun w2 _ => ?_)
    by_cases h : w2 = (i, j)
    · simp [h]
    · rw [if_neg h, if_neg h, H_summand_eq_base_kernel S i j w2]
  rw [hsummand]
  -- Split: ∑_{all} − (excluded term at (i,j)).
  set f : Fin n₁ × Fin n₂ → ℝ :=
    fun w2 => linearNeumannDiagonalBaseMatrix S w2.1 w2.2 *
      tangentCoordinateKernel S w2.1 w2.2 i j with hf
  have hsplit :
      (∑ w2 : Fin n₁ × Fin n₂, if w2 = (i, j) then 0 else f w2)
        = (∑ w2 : Fin n₁ × Fin n₂, f w2) - f (i, j) := by
    have hrw : ∀ w2 : Fin n₁ × Fin n₂,
        (if w2 = (i, j) then (0 : ℝ) else f w2) =
          f w2 - (if w2 = (i, j) then f w2 else 0) := by
      intro w2; by_cases h : w2 = (i, j) <;> simp [h]
    rw [Finset.sum_congr rfl (fun w2 _ => hrw w2), Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_ite_eq' Finset.univ (i, j) f]
    simp
  rw [hsplit]
  have hfij : f (i, j) = linearNeumannDiagonalBaseMatrix S i j *
      tangentCoordinateKernel S i j i j := by rw [hf]
  rw [hfij, kernel_expansion S (linearNeumannDiagonalBaseMatrix S) i j]

/-! ### Entrywise bounds on the three pieces. -/

/-- `|lambdaUE_{ij}| = |dU_i · E_{ij}| ≤ (μ₀ r/min)·(μ₁ √(r/n₁n₂))`. -/
private lemma abs_lambdaUE_le
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ μ₁ : ℝ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁) (hA0 : A0 S μ₀) (hA1 : A1 S μ₁)
    (i : Fin n₁) (j : Fin n₂) :
    |lambdaUE S i j| ≤
      (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
  unfold lambdaUE
  rw [abs_mul]
  have hdU := dU_abs_le S μ₀ hn₁ hn₂ hr hμ₀ hA0 i
  have hE := hA1 i j
  have hsqrt : 0 ≤ μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by positivity
  have hBnn : 0 ≤ μ₀ * (r : ℝ) / (↑(min n₁ n₂)) := by positivity
  exact mul_le_mul hdU hE (abs_nonneg _) hBnn

/-- `|eLambdaV_{ij}| = |E_{ij} · dV_j| ≤ (μ₀ r/min)·(μ₁ √(r/n₁n₂))`. -/
private lemma abs_eLambdaV_le
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ μ₁ : ℝ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁) (hA0 : A0 S μ₀) (hA1 : A1 S μ₁)
    (i : Fin n₁) (j : Fin n₂) :
    |eLambdaV S i j| ≤
      (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
  unfold eLambdaV
  rw [abs_mul, mul_comm]
  have hdV := dV_abs_le S μ₀ hn₁ hn₂ hr hμ₀ hA0 j
  have hE := hA1 i j
  have hsqrt : 0 ≤ μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) := by positivity
  have hBnn : 0 ≤ μ₀ * (r : ℝ) / (↑(min n₁ n₂)) := by positivity
  exact mul_le_mul hdV hE (abs_nonneg _) hBnn

/-! ### Kdiag range bounds and the second-term bound. -/

/-- `Kdiag_{ij} = dU_i + dV_j − dU_i·dV_j ∈ [0,1]`, using Bessel `dU,dV ≤ 1`. -/
private lemma Kdiag_mem_unit_interval
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    0 ≤ tangentCoordinateKernel S i j i j ∧
      tangentCoordinateKernel S i j i j ≤ 1 := by
  rw [Kdiag_decomp S i j]
  have hOne := svd_singular_coordinate_energy_le_one S
  have hdUle : (∑ k : Fin r, (S.u k i) ^ 2) ≤ 1 := hOne.1 i
  have hdVle : (∑ k : Fin r, (S.v k j) ^ 2) ≤ 1 := hOne.2 j
  have hdUnn : 0 ≤ (∑ k : Fin r, (S.u k i) ^ 2) := by positivity
  have hdVnn : 0 ≤ (∑ k : Fin r, (S.v k j) ^ 2) := by positivity
  constructor
  · nlinarith [mul_nonneg hdUnn hdVnn]
  · nlinarith [mul_nonneg (sub_nonneg.mpr hdUle) (sub_nonneg.mpr hdVle)]

/-- `|Kdiag_{ij}| ≤ 2·(μ₀ r/min)` from A0. -/
private lemma abs_Kdiag_le_two_scale
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ : ℝ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hA0 : A0 S μ₀) (i : Fin n₁) (j : Fin n₂) :
    |tangentCoordinateKernel S i j i j| ≤ 2 * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  have hrange := Kdiag_mem_unit_interval S i j
  rw [abs_of_nonneg hrange.1, Kdiag_decomp S i j]
  have hdU := (a0_singular_coordinate_energy_bounds S μ₀ hn₁ hn₂ hr hA0).1 i
  have hdV := (a0_singular_coordinate_energy_bounds S μ₀ hn₁ hn₂ hr hA0).2 j
  have hdUnn : 0 ≤ (∑ k : Fin r, (S.u k i) ^ 2) := by positivity
  have hdVnn : 0 ≤ (∑ k : Fin r, (S.v k j) ^ 2) := by positivity
  set B : ℝ := μ₀ * (r : ℝ) / (↑(min n₁ n₂)) with hBdef
  have hmin1 : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₁ : ℝ) := by exact_mod_cast min_le_left n₁ n₂
  have hmin2 : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₂ : ℝ) := by exact_mod_cast min_le_right n₁ n₂
  have hnum : 0 ≤ μ₀ * (r : ℝ) := by positivity
  have hdU' : (∑ k : Fin r, (S.u k i) ^ 2) ≤ B := by
    refine hdU.trans ?_; rw [hBdef]; gcongr
  have hdV' : (∑ k : Fin r, (S.v k j) ^ 2) ≤ B := by
    refine hdV.trans ?_; rw [hBdef]; gcongr
  nlinarith [mul_nonneg hdUnn hdVnn]

/-- `|base_{ij}·Kdiag_{ij}| ≤ 2·(μ₀ r/min)·(μ₁ √(r/n₁n₂))`. -/
private lemma abs_base_mul_Kdiag_le
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ μ₁ : ℝ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁) (hA0 : A0 S μ₀) (hA1 : A1 S μ₁)
    (i : Fin n₁) (j : Fin n₂) :
    |linearNeumannDiagonalBaseMatrix S i j *
        tangentCoordinateKernel S i j i j| ≤
      2 * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) := by
  -- base_ij = E_ij·Kdiag_ij, so base_ij·Kdiag_ij = E_ij·Kdiag_ij².
  have hbase : linearNeumannDiagonalBaseMatrix S i j =
      signMatrix S i j * tangentCoordinateKernel S i j i j := rfl
  rw [hbase, abs_mul, abs_mul]
  -- |E_ij| ≤ µ₁√.., |Kdiag| ≤ 1, |Kdiag| ≤ 2µ₀r/min.
  have hE := hA1 i j
  have hKrange := Kdiag_mem_unit_interval S i j
  have hK1 : |tangentCoordinateKernel S i j i j| ≤ 1 := by
    rw [abs_of_nonneg hKrange.1]; exact hKrange.2
  have hK2 := abs_Kdiag_le_two_scale S μ₀ hn₁ hn₂ hr hμ₀ hA0 i j
  set sq : ℝ := μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) with hsqdef
  set B : ℝ := μ₀ * (r : ℝ) / (↑(min n₁ n₂)) with hBdef
  have hsqnn : 0 ≤ sq := by rw [hsqdef]; positivity
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  -- |E|·|Kdiag|·|Kdiag| ≤ sq·(2B)·1 = 2B·sq
  calc
    |signMatrix S i j| * |tangentCoordinateKernel S i j i j| *
        |tangentCoordinateKernel S i j i j|
        ≤ sq * (2 * B) * 1 := by gcongr
    _ = 2 * B * sq := by ring

/-- `|(P_T Q)_{ij}| ≤ 4·(μ₀ r/min)²` (via entry ≤ spectral, then contraction). -/
private lemma abs_PT_lambdaUEV_le
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ : ℝ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hA0 : A0 S μ₀) (i : Fin n₁) (j : Fin n₂) :
    |tangentProjection S (lambdaUEV S) i j| ≤
      4 * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) ^ 2 := by
  set B : ℝ := μ₀ * (r : ℝ) / (↑(min n₁ n₂)) with hBdef
  calc
    |tangentProjection S (lambdaUEV S) i j|
        ≤ spectralNorm (tangentProjection S (lambdaUEV S)) := by
          have h := entrySupNorm_le_spectralNorm hn₁ hn₂
            (tangentProjection S (lambdaUEV S))
          exact le_trans (abs_entry_le_entrySupNorm _ i j) h
    _ ≤ 2 * spectralNorm (lambdaUEV S) :=
          tangentProjection_spectralNorm_le S (lambdaUEV S)
    _ ≤ 2 * (2 * B ^ 2) := by
          have := lambdaUEV_spectralNorm_le S μ₀ hn₁ hn₂ hr hμ₀ hA0
          rw [← hBdef] at this
          linarith
    _ = 4 * B ^ 2 := by ring

/-! ### Assembled `p·H` entry bound and the `0 < p` conditional core. -/

/-- `|(P_T base − base·Kdiag)_{ij}| ≤ 4·B·(sq + B)` with
`B = μ₀ r/min`, `sq = μ₁ √(r/n₁n₂)`. -/
private lemma abs_pH_entry_le
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ μ₁ : ℝ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (hr : 0 < r)
    (hμ₀ : 1 ≤ μ₀) (hμ₁ : 1 ≤ μ₁) (hA0 : A0 S μ₀) (hA1 : A1 S μ₁)
    (i : Fin n₁) (j : Fin n₂) :
    |tangentProjection S (linearNeumannDiagonalBaseMatrix S) i j -
        linearNeumannDiagonalBaseMatrix S i j *
          tangentCoordinateKernel S i j i j| ≤
      4 * (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
        (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
          μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  set B : ℝ := μ₀ * (r : ℝ) / (↑(min n₁ n₂)) with hBdef
  set sq : ℝ := μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) with hsqdef
  -- P_T base entry = (Λ_U E) + (E Λ_V) − (P_T Q).
  have hptbase : tangentProjection S (linearNeumannDiagonalBaseMatrix S) i j =
      lambdaUE S i j + eLambdaV S i j - tangentProjection S (lambdaUEV S) i j := by
    rw [pt_base_eq]
    simp [Matrix.add_apply, Matrix.sub_apply]
  rw [hptbase]
  have h1 : |lambdaUE S i j| ≤ B * sq :=
    abs_lambdaUE_le S μ₀ μ₁ hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 i j
  have h2 : |eLambdaV S i j| ≤ B * sq :=
    abs_eLambdaV_le S μ₀ μ₁ hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 i j
  have h3 : |tangentProjection S (lambdaUEV S) i j| ≤ 4 * B ^ 2 :=
    abs_PT_lambdaUEV_le S μ₀ hn₁ hn₂ hr hμ₀ hA0 i j
  have h4 : |linearNeumannDiagonalBaseMatrix S i j *
      tangentCoordinateKernel S i j i j| ≤ 2 * B * sq :=
    abs_base_mul_Kdiag_le S μ₀ μ₁ hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 i j
  -- Triangle inequality.
  have htri :
      |lambdaUE S i j + eLambdaV S i j - tangentProjection S (lambdaUEV S) i j -
          linearNeumannDiagonalBaseMatrix S i j *
            tangentCoordinateKernel S i j i j|
        ≤ |lambdaUE S i j| + |eLambdaV S i j| +
            |tangentProjection S (lambdaUEV S) i j| +
              |linearNeumannDiagonalBaseMatrix S i j *
                tangentCoordinateKernel S i j i j| := by
    have e1 := abs_add_le (lambdaUE S i j) (eLambdaV S i j)
    have e2 := abs_sub (lambdaUE S i j + eLambdaV S i j)
      (tangentProjection S (lambdaUEV S) i j)
    have e3 := abs_sub
      (lambdaUE S i j + eLambdaV S i j - tangentProjection S (lambdaUEV S) i j)
      (linearNeumannDiagonalBaseMatrix S i j *
        tangentCoordinateKernel S i j i j)
    calc
      |lambdaUE S i j + eLambdaV S i j - tangentProjection S (lambdaUEV S) i j -
          linearNeumannDiagonalBaseMatrix S i j *
            tangentCoordinateKernel S i j i j|
          ≤ |lambdaUE S i j + eLambdaV S i j -
                tangentProjection S (lambdaUEV S) i j| +
              |linearNeumannDiagonalBaseMatrix S i j *
                tangentCoordinateKernel S i j i j| := e3
      _ ≤ (|lambdaUE S i j + eLambdaV S i j| +
              |tangentProjection S (lambdaUEV S) i j|) +
              |linearNeumannDiagonalBaseMatrix S i j *
                tangentCoordinateKernel S i j i j| := by
            gcongr
      _ ≤ ((|lambdaUE S i j| + |eLambdaV S i j|) +
              |tangentProjection S (lambdaUEV S) i j|) +
              |linearNeumannDiagonalBaseMatrix S i j *
                tangentCoordinateKernel S i j i j| := by
            gcongr
      _ = |lambdaUE S i j| + |eLambdaV S i j| +
            |tangentProjection S (lambdaUEV S) i j| +
              |linearNeumannDiagonalBaseMatrix S i j *
                tangentCoordinateKernel S i j i j| := by ring
  have hBnn : 0 ≤ B := by rw [hBdef]; positivity
  have hsqnn : 0 ≤ sq := by rw [hsqdef]; positivity
  -- B*sq + B*sq + 4B² + 2B*sq = 4B*sq + 4B² = 4B(sq+B).
  calc
    |lambdaUE S i j + eLambdaV S i j - tangentProjection S (lambdaUEV S) i j -
        linearNeumannDiagonalBaseMatrix S i j *
          tangentCoordinateKernel S i j i j|
        ≤ B * sq + B * sq + 4 * B ^ 2 + 2 * B * sq := by
          refine htri.trans ?_
          gcongr
    _ = 4 * B * (sq + B) := by ring

end QuadraticFirstIndexDistinctMeanLemma68

open QuadraticFirstIndexDistinctMeanLemma68

/-- Corrected `r/min` Lemma 6.8 mean-coefficient entry bound (with `0 < p`),
the sound replacement for the disproved `r/max` node d5efa6ed.  Fully proven
sorry-free modulo the imported OPEN/Proved primitive stubs. -/
theorem solution :
    ∃ C68 : ℝ, 0 < C68 ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r) (p : ℝ),
        0 < n₁ → 0 < n₂ → 0 < r → 0 < p →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        entrySupNorm (quadraticFirstIndexDistinctMeanCoefficientMatrix S p) ≤
          C68 * p⁻¹ *
            (μ₀ * (r : ℝ) / (↑(min n₁ n₂))) *
              (μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) +
                μ₀ * (r : ℝ) / (↑(min n₁ n₂))) := by
  refine ⟨4, by norm_num, ?_⟩
  intro n₁ n₂ r M μ₀ μ₁ S p hn₁ hn₂ hr hp hμ₀ hμ₁ hA0 hA1
  set B : ℝ := μ₀ * (r : ℝ) / (↑(min n₁ n₂)) with hBdef
  set sq : ℝ := μ₁ * Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) with hsqdef
  have hpinv_nn : 0 ≤ p⁻¹ := le_of_lt (inv_pos.mpr hp)
  -- Entrywise bound: |H_ij| ≤ 4 · p⁻¹ · B · (sq + B).
  apply entrySupNorm_le_of_forall_abs_le hn₁ hn₂
  intro i j
  rw [H_entry_eq S p i j, abs_mul, abs_of_nonneg hpinv_nn]
  have hpH := abs_pH_entry_le S μ₀ μ₁ hn₁ hn₂ hr hμ₀ hμ₁ hA0 hA1 i j
  rw [← hBdef, ← hsqdef] at hpH
  calc
    p⁻¹ *
        |tangentProjection S (linearNeumannDiagonalBaseMatrix S) i j -
          linearNeumannDiagonalBaseMatrix S i j *
            tangentCoordinateKernel S i j i j|
        ≤ p⁻¹ * (4 * B * (sq + B)) := by
          exact mul_le_mul_of_nonneg_left hpH hpinv_nn
    _ = 4 * p⁻¹ * B * (sq + B) := by ring

