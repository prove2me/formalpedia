-- Prove2me | solution 1 for quadratic_neumann_middle_index_distinct_mean_coefficients_section63_bound_under_general_sample_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:58:00.71331+00:00
-- url     : https://prove2.me/submissions/6f2aa2ce-9996-4298-8631-84ce7424d476

import Mathlib
import Definitions.Def_matrix_completion_neumann

set_option autoImplicit false

section

section
open MatrixCompletion

open scoped Classical BigOperators

private lemma P.D0.coherence_coordinate_energy_le
    {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (u : Fin r → Fin N → ℝ) {μ : ℝ} :
    coherence N r u ≤ μ →
    ∀ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 ≤ μ * (r : ℝ) / (N : ℝ) := by
  intro hcoh i
  have hscale_pos : 0 < (N : ℝ) / (r : ℝ) :=
    div_pos (Nat.cast_pos.mpr hN) (Nat.cast_pos.mpr hr)
  have hleSup :
      (∑ k : Fin r, (u k i) ^ 2) ≤
        ⨆ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 :=
    Finite.le_ciSup (f := fun i : Fin N => ∑ k : Fin r, (u k i) ^ 2) i
  have hsup :
      (⨆ i : Fin N, ∑ k : Fin r, (u k i) ^ 2) ≤
        μ / ((N : ℝ) / (r : ℝ)) := by
    rw [le_div_iff₀ hscale_pos]
    simpa [coherence, mul_comm, mul_left_comm, mul_assoc] using hcoh
  calc
    (∑ k : Fin r, (u k i) ^ 2)
        ≤ μ / ((N : ℝ) / (r : ℝ)) := le_trans hleSup hsup
    _ = μ * (r : ℝ) / (N : ℝ) := by
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hN
      have hr' : (r : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hr
      field_simp [hN', hr']

theorem P.D0.a0_singular_coordinate_energy_bounds
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ : ℝ) :
    0 < n₁ → 0 < n₂ → 0 < r → A0 S μ₀ →
      (∀ i : Fin n₁,
        ∑ k : Fin r, (S.u k i) ^ 2 ≤ μ₀ * (r : ℝ) / (n₁ : ℝ)) ∧
      (∀ j : Fin n₂,
        ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₀ * (r : ℝ) / (n₂ : ℝ)) := by
  intro hn₁ hn₂ hr hA0
  exact ⟨coherence_coordinate_energy_le hn₁ hr S.u hA0.1,
    coherence_coordinate_energy_le hn₂ hr S.v hA0.2⟩
end
export P.D0 (a0_singular_coordinate_energy_bounds)

section
open MatrixCompletion

open scoped Classical BigOperators

private lemma P.D1.coordinate_energy_le_one_of_orthonormal
    {N r : ℕ} (u : Fin r → Fin N → ℝ)
    (horth : ∀ k l : Fin r,
      ∑ i : Fin N, u k i * u l i = if k = l then 1 else 0) :
    ∀ i : Fin N, ∑ k : Fin r, (u k i) ^ 2 ≤ (1 : ℝ) := by
  intro i
  let P : Fin N → ℝ := fun a => ∑ k : Fin r, u k i * u k a
  have hP_nonneg : 0 ≤ P i := by
    dsimp [P]
    exact Finset.sum_nonneg fun k _ => by nlinarith [sq_nonneg (u k i)]
  have hsum_idem : ∑ a : Fin N, (P a) ^ 2 = P i := by
    calc
      ∑ a : Fin N, (P a) ^ 2
          = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r,
              (u k i * u l i) * (u k a * u l a) := by
            dsimp [P]
            apply Finset.sum_congr rfl
            intro a _ha
            simp_rw [sq, Finset.sum_mul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _hk
            apply Finset.sum_congr rfl
            intro l _hl
            ring
      _ = ∑ k : Fin r, ∑ l : Fin r,
            (u k i * u l i) * (∑ a : Fin N, u k a * u l a) := by
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro k _hk
            rw [Finset.sum_comm]
            apply Finset.sum_congr rfl
            intro l _hl
            rw [Finset.mul_sum]
      _ = ∑ k : Fin r, ∑ l : Fin r,
            (u k i * u l i) * (if k = l then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro k _hk
            apply Finset.sum_congr rfl
            intro l _hl
            rw [horth k l]
      _ = ∑ k : Fin r, (u k i) ^ 2 := by
            apply Finset.sum_congr rfl
            intro k _hk
            rw [Finset.sum_eq_single k]
            · simp [pow_two]
            · intro l _hl hne
              have hkne : k ≠ l := fun h => hne h.symm
              simp [hkne]
            · intro hnot
              exact (hnot (Finset.mem_univ k)).elim
      _ = P i := by
            dsimp [P]
            apply Finset.sum_congr rfl
            intro k _hk
            ring
  have hsq_le_sum : (P i) ^ 2 ≤ ∑ a : Fin N, (P a) ^ 2 := by
    exact Finset.single_le_sum (fun a _ha => sq_nonneg (P a)) (Finset.mem_univ i)
  have hsq_le : (P i) ^ 2 ≤ P i := by
    simpa [hsum_idem] using hsq_le_sum
  have hPi_le_one : P i ≤ (1 : ℝ) := by
    nlinarith
  simpa [P, pow_two] using hPi_le_one

theorem P.D1.svd_singular_coordinate_energy_le_one
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) :
      (∀ i : Fin n₁, ∑ k : Fin r, (S.u k i) ^ 2 ≤ (1 : ℝ)) ∧
      (∀ j : Fin n₂, ∑ k : Fin r, (S.v k j) ^ 2 ≤ (1 : ℝ)) := by
  exact ⟨coordinate_energy_le_one_of_orthonormal S.u S.u_orthonormal,
    coordinate_energy_le_one_of_orthonormal S.v S.v_orthonormal⟩
end
export P.D1 (svd_singular_coordinate_energy_le_one)

section
open MatrixCompletion

open scoped Classical BigOperators

private lemma P.D2.matrixInner_coordinate_right
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

private lemma P.D2.leftSingularProjection_coordinate_same
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    leftSingularProjection S (coordinateMatrix i j) i j =
      ∑ k : Fin r, (S.u k i) ^ 2 := by
  unfold leftSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single i]
  · simp [pow_two]
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma P.D2.rightSingularProjection_coordinate_same
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    rightSingularProjection S (coordinateMatrix i j) i j =
      ∑ k : Fin r, (S.v k j) ^ 2 := by
  unfold rightSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single j]
  · simp [pow_two]
  · intro b _hb hb
    simp [hb]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

private lemma P.D2.twoSidedSingularProjection_coordinate_same
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    twoSidedSingularProjection S (coordinateMatrix i j) i j =
      (∑ k : Fin r, (S.u k i) ^ 2) *
        (∑ k : Fin r, (S.v k j) ^ 2) := by
  unfold twoSidedSingularProjection coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp [pow_two, Finset.mul_sum, Finset.sum_mul]
    · intro b _hb hb
      simp [hb]
    · intro hj
      exact (hj (Finset.mem_univ j)).elim
  · intro a _ha ha
    simp [ha]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

private lemma P.D2.tangent_coordinate_kernel_diagonal_formula
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (i : Fin n₁) (j : Fin n₂) :
    tangentCoordinateKernel S i j i j =
      (∑ k : Fin r, (S.u k i) ^ 2) +
        (∑ k : Fin r, (S.v k j) ^ 2) -
          (∑ k : Fin r, (S.u k i) ^ 2) *
            (∑ k : Fin r, (S.v k j) ^ 2) := by
  rw [tangentCoordinateKernel, matrixInner_coordinate_right]
  simp [tangentProjection, leftSingularProjection_coordinate_same,
    rightSingularProjection_coordinate_same,
    twoSidedSingularProjection_coordinate_same]

theorem P.D2.tangent_coordinate_kernel_diagonal_bound_from_singular_coordinate_energies :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ →
        (∀ i : Fin n₁,
          ∑ k : Fin r, (S.u k i) ^ 2 ≤ μ₀ * (r : ℝ) / (n₁ : ℝ)) →
        (∀ j : Fin n₂,
          ∑ k : Fin r, (S.v k j) ^ 2 ≤ μ₀ * (r : ℝ) / (n₂ : ℝ)) →
        (∀ i : Fin n₁, ∑ k : Fin r, (S.u k i) ^ 2 ≤ (1 : ℝ)) →
        (∀ j : Fin n₂, ∑ k : Fin r, (S.v k j) ^ 2 ≤ (1 : ℝ)) →
        ∀ i j,
          |tangentCoordinateKernel S i j i j| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  refine ⟨3, by norm_num, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hu hv huOne hvOne i j
  let U : ℝ := ∑ k : Fin r, (S.u k i) ^ 2
  let V : ℝ := ∑ k : Fin r, (S.v k j) ^ 2
  let scale : ℝ := μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ))
  have hmin_pos_nat : 0 < min n₁ n₂ := lt_min hn₁ hn₂
  have hscale_nonneg : 0 ≤ scale := by
    dsimp [scale]
    positivity
  have hU_nonneg : 0 ≤ U := by
    dsimp [U]
    exact Finset.sum_nonneg fun k _ => sq_nonneg (S.u k i)
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    exact Finset.sum_nonneg fun k _ => sq_nonneg (S.v k j)
  have hU_one : U ≤ 1 := by
    simpa [U] using huOne i
  have hV_one : V ≤ 1 := by
    simpa [V] using hvOne j
  have hU_scale : U ≤ scale := by
    have hmin_le : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₁ : ℝ) := by
      exact_mod_cast min_le_left n₁ n₂
    have hmono :
        μ₀ * (r : ℝ) / (n₁ : ℝ) ≤
          μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
      gcongr
    exact le_trans (by simpa [U] using hu i) hmono
  have hV_scale : V ≤ scale := by
    have hmin_le : (((min n₁ n₂ : ℕ) : ℝ)) ≤ (n₂ : ℝ) := by
      exact_mod_cast min_le_right n₁ n₂
    have hmono :
        μ₀ * (r : ℝ) / (n₂ : ℝ) ≤
          μ₀ * (r : ℝ) / (((min n₁ n₂ : ℕ) : ℝ)) := by
      gcongr
    exact le_trans (by simpa [V] using hv j) hmono
  have hformula := tangent_coordinate_kernel_diagonal_formula S i j
  have hnonneg_expr : 0 ≤ U + V - U * V := by
    have h1V : 0 ≤ 1 - V := by linarith
    nlinarith [mul_nonneg hU_nonneg h1V, hV_nonneg]
  calc
    |tangentCoordinateKernel S i j i j|
        = |U + V - U * V| := by
          rw [hformula]
    _ = U + V - U * V := abs_of_nonneg hnonneg_expr
    _ ≤ U + V := by nlinarith [mul_nonneg hU_nonneg hV_nonneg]
    _ ≤ scale + scale := by linarith
    _ ≤ 3 * scale := by nlinarith [hscale_nonneg]
    _ = 3 * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
      dsimp [scale]
      ring
end
export P.D2 (tangent_coordinate_kernel_diagonal_bound_from_singular_coordinate_energies)

section
open MatrixCompletion

open scoped Classical BigOperators

theorem P.D3.tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ i j,
          |tangentCoordinateKernel S i j i j| ≤
            Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) := by
  rcases tangent_coordinate_kernel_diagonal_bound_from_singular_coordinate_energies with
    ⟨Cker, hCker_pos, hker⟩
  refine ⟨Cker, hCker_pos, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 i j
  have hEnergy :=
    a0_singular_coordinate_energy_bounds S μ₀ hn₁ hn₂ hr hA0
  have hOne := svd_singular_coordinate_energy_le_one S
  exact hker n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀
    hEnergy.1 hEnergy.2 hOne.1 hOne.2 i j
end
export P.D3 (tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim)

section
open MatrixCompletion
open scoped BigOperators

section

theorem P.D4.MC.matrixInner_comm {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    matrixInner X Y = matrixInner Y X := by
  unfold matrixInner
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem P.D4.MC.matrixInner_add_right {n1 n2 : Nat} (X Y Z : RealMatrix n1 n2) :
    matrixInner X (Y + Z) = matrixInner X Y + matrixInner X Z := by
  unfold matrixInner
  simp only [Matrix.add_apply, mul_add]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]

theorem P.D4.MC.matrixInner_sub_right {n1 n2 : Nat} (X Y Z : RealMatrix n1 n2) :
    matrixInner X (Y - Z) = matrixInner X Y - matrixInner X Z := by
  unfold matrixInner
  simp only [Matrix.sub_apply, mul_sub]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_sub_distrib]

theorem P.D4.MC.matrixInner_zero_right {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    matrixInner X 0 = 0 := by
  unfold matrixInner
  simp

private theorem P.D4.MC.sum_pair_collapse {n1 n2 : Nat}
    (G : Fin n1 → Fin n2 → Real) :
    (∑ i, ∑ j, G i j)
      = ∑ p : Fin n1 × Fin n2, G p.1 p.2 := by
  rw [← Finset.sum_product']
  rfl

private theorem P.D4.MC.sum4_swap {n1 n2 : Nat}
    (F : Fin n1 → Fin n2 → Fin n1 → Fin n2 → Real) :
    (∑ i, ∑ j, ∑ a, ∑ b, F i j a b) = (∑ a, ∑ b, ∑ i, ∑ j, F i j a b) := by
  have h1 : (∑ i, ∑ j, ∑ a, ∑ b, F i j a b)
      = ∑ p : Fin n1 × Fin n2, ∑ q : Fin n1 × Fin n2, F p.1 p.2 q.1 q.2 := by
    rw [sum_pair_collapse (fun i j => ∑ a, ∑ b, F i j a b)]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [sum_pair_collapse (fun a b => F p.1 p.2 a b)]
  have h2 : (∑ a, ∑ b, ∑ i, ∑ j, F i j a b)
      = ∑ q : Fin n1 × Fin n2, ∑ p : Fin n1 × Fin n2, F p.1 p.2 q.1 q.2 := by
    rw [sum_pair_collapse (fun a b => ∑ i, ∑ j, F i j a b)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [sum_pair_collapse (fun i j => F i j q.1 q.2)]
  rw [h1, h2, Finset.sum_comm]

theorem P.D4.MC.matrixInner_kernel_selfAdjoint {n1 n2 : Nat}
    (K : Fin n1 → Fin n2 → Fin n1 → Fin n2 → Real)
    (hK : ∀ i j a b, K i j a b = K a b i j)
    (X Y : RealMatrix n1 n2) :
    matrixInner (fun i j => ∑ a, ∑ b, K i j a b * X a b) Y
      = matrixInner X (fun i j => ∑ a, ∑ b, K i j a b * Y a b) := by
  unfold matrixInner
  simp only [Finset.sum_mul, Finset.mul_sum]

  rw [sum4_swap (fun i j a b => X i j * (K i j a b * Y a b))]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  refine Finset.sum_congr rfl (fun j _ => ?_)
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  rw [hK a b i j]
  ring

theorem P.D4.MC.leftSingularProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner (leftSingularProjection S X) Y = matrixInner X (leftSingularProjection S Y) := by
  have hL : ∀ (Z : RealMatrix n1 n2),
      leftSingularProjection S Z
        = (fun i j => ∑ a, ∑ b, ((∑ k, S.u k i * S.u k a) * (if b = j then 1 else 0)) * Z a b) := by
    intro Z
    funext i j
    unfold leftSingularProjection
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  rw [hL X, hL Y]
  refine matrixInner_kernel_selfAdjoint _ ?_ X Y
  intro i j a b
  by_cases hbj : b = j <;> by_cases hji : j = b
  · subst hbj; simp; refine Finset.sum_congr rfl (fun k _ => ?_); ring
  · subst hbj; exact absurd rfl hji
  · exact absurd hji.symm hbj
  · simp [hbj, fun h : j = b => hji h]

theorem P.D4.MC.rightSingularProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner (rightSingularProjection S X) Y = matrixInner X (rightSingularProjection S Y) := by
  have hR : ∀ (Z : RealMatrix n1 n2),
      rightSingularProjection S Z
        = (fun i j => ∑ a, ∑ b, ((if a = i then 1 else 0) * (∑ k, S.v k b * S.v k j)) * Z a b) := by
    intro Z
    funext i j
    unfold rightSingularProjection

    symm
    rw [Finset.sum_eq_single i]
    · refine Finset.sum_congr rfl (fun b _ => ?_); simp; ring
    · intro a _ ha; refine Finset.sum_eq_zero (fun b _ => ?_); simp [ha]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [hR X, hR Y]
  refine matrixInner_kernel_selfAdjoint _ ?_ X Y
  intro i j a b
  by_cases hai : a = i <;> by_cases hia : i = a
  · subst hai; simp; refine Finset.sum_congr rfl (fun k _ => ?_); ring
  · subst hai; exact absurd rfl hia
  · exact absurd hia.symm hai
  · simp [hai, fun h : i = a => hia h]

theorem P.D4.MC.twoSidedSingularProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner (twoSidedSingularProjection S X) Y
      = matrixInner X (twoSidedSingularProjection S Y) := by
  have hT : ∀ (Z : RealMatrix n1 n2),
      twoSidedSingularProjection S Z
        = (fun i j => ∑ a, ∑ b,
            ((∑ k, S.u k i * S.u k a) * (∑ l, S.v l b * S.v l j)) * Z a b) := by
    intro Z
    funext i j
    unfold twoSidedSingularProjection
    refine Finset.sum_congr rfl (fun a _ => ?_)
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [hT X, hT Y]
  refine matrixInner_kernel_selfAdjoint _ ?_ X Y
  intro i j a b

  have hu : (∑ k, S.u k i * S.u k a) = (∑ k, S.u k a * S.u k i) := by
    refine Finset.sum_congr rfl (fun k _ => ?_); ring
  have hv : (∑ l, S.v l b * S.v l j) = (∑ l, S.v l j * S.v l b) := by
    refine Finset.sum_congr rfl (fun l _ => ?_); ring
  rw [hu, hv]

private theorem P.D4.MC.sum3_rot {γ κ μ : Type*} [Fintype γ] [Fintype κ] [Fintype μ]
    (F : γ → κ → μ → Real) :
    (∑ c, ∑ k, ∑ l, F c k l) = ∑ k, ∑ l, ∑ c, F c k l := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_comm]

private theorem P.D4.MC.u_proj_idem {n1 r : Nat} (u : Fin r → (Fin n1 → Real))
    (hu : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0) (i a : Fin n1) :
    (∑ c, (∑ k, u k i * u k c) * (∑ l, u l c * u l a)) = ∑ k, u k i * u k a := by
  have hflat : (∑ c, (∑ k, u k i * u k c) * (∑ l, u l c * u l a))
      = ∑ c, ∑ k, ∑ l, (u k i * u l a) * (u k c * u l c) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hflat, sum3_rot (fun c k l => (u k i * u l a) * (u k c * u l c))]
  have hstep : (∑ k, ∑ l, ∑ c, (u k i * u l a) * (u k c * u l c))
      = ∑ k, ∑ l, (u k i * u l a) * (∑ c, u k c * u l c) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
  rw [hstep]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · rw [hu k k]; simp
  · intro l _ hl; rw [hu k l]; simp [Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ k) h

private theorem P.D4.MC.v_proj_idem {n2 r : Nat} (v : Fin r → (Fin n2 → Real))
    (hv : ∀ k l, ∑ j, v k j * v l j = if k = l then 1 else 0) (b j : Fin n2) :
    (∑ c, (∑ k, v k b * v k c) * (∑ l, v l c * v l j)) = ∑ k, v k b * v k j := by
  have hflat : (∑ c, (∑ k, v k b * v k c) * (∑ l, v l c * v l j))
      = ∑ c, ∑ k, ∑ l, (v k b * v l j) * (v k c * v l c) := by
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    ring
  rw [hflat, sum3_rot (fun c k l => (v k b * v l j) * (v k c * v l c))]
  have hstep : (∑ k, ∑ l, ∑ c, (v k b * v l j) * (v k c * v l c))
      = ∑ k, ∑ l, (v k b * v l j) * (∑ c, v k c * v l c) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Finset.mul_sum]
  rw [hstep]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_eq_single k]
  · rw [hv k k]; simp
  · intro l _ hl; rw [hv k l]; simp [Ne.symm hl]
  · intro h; exact absurd (Finset.mem_univ k) h

private theorem P.D4.MC.LL {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (leftSingularProjection S X) = leftSingularProjection S X := by
  funext i j
  unfold leftSingularProjection

  have hflat : (∑ a, (∑ k, S.u k i * S.u k a) * ∑ a', (∑ k, S.u k a * S.u k a') * X a' j)
      = ∑ a, ∑ a', (∑ k, S.u k i * S.u k a) * ((∑ k, S.u k a * S.u k a') * X a' j) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
  have h1 : (∑ a, (∑ k, S.u k i * S.u k a) * ∑ a', (∑ k, S.u k a * S.u k a') * X a' j)
      = ∑ a', (∑ c, (∑ k, S.u k i * S.u k c) * (∑ l, S.u l c * S.u l a')) * X a' j := by
    rw [hflat, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a' _ => ?_)
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    ring
  rw [h1]
  refine Finset.sum_congr rfl (fun a' _ => ?_)
  rw [u_proj_idem S.u S.u_orthonormal i a']

private theorem P.D4.MC.RR {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (rightSingularProjection S X) = rightSingularProjection S X := by
  funext i j
  unfold rightSingularProjection
  have hflat : (∑ b, (∑ b', X i b' * ∑ k, S.v k b' * S.v k b) * ∑ k, S.v k b * S.v k j)
      = ∑ b, ∑ b', (X i b' * (∑ k, S.v k b' * S.v k b)) * (∑ k, S.v k b * S.v k j) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_mul]
  have h1 : (∑ b, (∑ b', X i b' * ∑ k, S.v k b' * S.v k b) * ∑ k, S.v k b * S.v k j)
      = ∑ b', X i b' * (∑ c, (∑ k, S.v k b' * S.v k c) * (∑ l, S.v l c * S.v l j)) := by
    rw [hflat, Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b' _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    ring
  rw [h1]
  refine Finset.sum_congr rfl (fun b' _ => ?_)
  rw [v_proj_idem S.v S.v_orthonormal b' j]

private theorem P.D4.MC.LR {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (rightSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  unfold leftSingularProjection rightSingularProjection twoSidedSingularProjection

  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  ring

private theorem P.D4.MC.RL {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (leftSingularProjection S X)
      = twoSidedSingularProjection S X := by
  funext i j
  unfold rightSingularProjection leftSingularProjection twoSidedSingularProjection

  have hflat : (∑ b, (∑ a, (∑ k, S.u k i * S.u k a) * X a b) * ∑ k, S.v k b * S.v k j)
      = ∑ b, ∑ a, ((∑ k, S.u k i * S.u k a) * X a b) * (∑ k, S.v k b * S.v k j) := by
    refine Finset.sum_congr rfl (fun b _ => ?_)
    rw [Finset.sum_mul]
  rw [hflat, Finset.sum_comm]

private theorem P.D4.MC.LT2 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    leftSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← LR S X, LL S (rightSingularProjection S X)]

private theorem P.D4.MC.T2L {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (leftSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← RL S (leftSingularProjection S X), LL S X, RL S X]

private theorem P.D4.MC.RT2 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    rightSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← RL S X, RR S (leftSingularProjection S X)]

private theorem P.D4.MC.T2R {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (rightSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← RL S (rightSingularProjection S X), LR S X, RT2 S X]

private theorem P.D4.MC.T2T2 {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (X : RealMatrix n1 n2) :
    twoSidedSingularProjection S (twoSidedSingularProjection S X)
      = twoSidedSingularProjection S X := by
  rw [← RL S (twoSidedSingularProjection S X), LT2 S X, RT2 S X]

private theorem P.D4.MC.left_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A + B)
      = leftSingularProjection S A + leftSingularProjection S B := by
  funext i j
  simp only [Matrix.add_apply]
  unfold leftSingularProjection
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Matrix.add_apply]; ring

private theorem P.D4.MC.left_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    leftSingularProjection S (A - B)
      = leftSingularProjection S A - leftSingularProjection S B := by
  funext i j
  simp only [Matrix.sub_apply]
  unfold leftSingularProjection
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [Matrix.sub_apply]; ring

private theorem P.D4.MC.right_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A + B)
      = rightSingularProjection S A + rightSingularProjection S B := by
  funext i j
  simp only [Matrix.add_apply]
  unfold rightSingularProjection
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Matrix.add_apply]; ring

private theorem P.D4.MC.right_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    rightSingularProjection S (A - B)
      = rightSingularProjection S A - rightSingularProjection S B := by
  funext i j
  simp only [Matrix.sub_apply]
  unfold rightSingularProjection
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Matrix.sub_apply]; ring

private theorem P.D4.MC.two_add {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A + B)
      = twoSidedSingularProjection S A + twoSidedSingularProjection S B := by
  funext i j
  simp only [Matrix.add_apply]
  unfold twoSidedSingularProjection
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Matrix.add_apply]; ring

private theorem P.D4.MC.two_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    twoSidedSingularProjection S (A - B)
      = twoSidedSingularProjection S A - twoSidedSingularProjection S B := by
  funext i j
  simp only [Matrix.sub_apply]
  unfold twoSidedSingularProjection
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  simp only [Matrix.sub_apply]; ring

theorem P.D4.MC.tangentProjection_sub {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (A B : RealMatrix n1 n2) :
    tangentProjection S (A - B) = tangentProjection S A - tangentProjection S B := by
  unfold tangentProjection
  rw [left_sub, right_sub, two_sub]
  abel

theorem P.D4.MC.tangentProjection_selfAdjoint {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X Y : RealMatrix n1 n2) :
    matrixInner (tangentProjection S X) Y = matrixInner X (tangentProjection S Y) := by
  unfold tangentProjection

  rw [matrixInner_comm (leftSingularProjection S X + rightSingularProjection S X
        - twoSidedSingularProjection S X) Y]
  rw [matrixInner_sub_right, matrixInner_add_right]

  rw [matrixInner_sub_right, matrixInner_add_right]

  rw [matrixInner_comm Y (leftSingularProjection S X),
      matrixInner_comm Y (rightSingularProjection S X),
      matrixInner_comm Y (twoSidedSingularProjection S X)]
  rw [leftSingularProjection_selfAdjoint, rightSingularProjection_selfAdjoint,
      twoSidedSingularProjection_selfAdjoint]

theorem P.D4.MC.tangentProjection_idem {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (X : RealMatrix n1 n2) :
    tangentProjection S (tangentProjection S X) = tangentProjection S X := by

  set L := leftSingularProjection S X with hLdef
  set R := rightSingularProjection S X with hRdef
  set T := twoSidedSingularProjection S X with hTdef

  conv_lhs => rw [show tangentProjection S X = L + R - T from rfl]
  unfold tangentProjection

  rw [left_sub, left_add, right_sub, right_add, two_sub, two_add]

  rw [hLdef, hRdef, hTdef]
  rw [LL S X, LR S X, LT2 S X,
      RL S X, RR S X, RT2 S X,
      T2L S X, T2R S X, T2T2 S X]

  abel

theorem P.D4.MC.tangentCoordinateKernel_eq_proj_inner {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (i : Fin n1) (j : Fin n2) (a : Fin n1) (b : Fin n2) :
    tangentCoordinateKernel S i j a b
      = matrixInner (tangentProjection S (coordinateMatrix i j))
          (tangentProjection S (coordinateMatrix a b)) := by
  unfold tangentCoordinateKernel

  have hsplit : (coordinateMatrix a b : RealMatrix n1 n2)
      = tangentProjection S (coordinateMatrix a b)
        + (coordinateMatrix a b - tangentProjection S (coordinateMatrix a b)) := by
    abel
  conv_lhs => rw [hsplit]
  rw [matrixInner_add_right]

  have hcross : matrixInner (tangentProjection S (coordinateMatrix i j))
      (coordinateMatrix a b - tangentProjection S (coordinateMatrix a b)) = 0 := by
    rw [tangentProjection_selfAdjoint S (coordinateMatrix i j)
          (coordinateMatrix a b - tangentProjection S (coordinateMatrix a b))]
    rw [tangentProjection_sub, tangentProjection_idem]
    rw [sub_self, matrixInner_zero_right]
  rw [hcross, add_zero]

theorem P.D4.MC.matrixInner_coordinateMatrix {n1 n2 : Nat} (X : RealMatrix n1 n2)
    (i : Fin n1) (j : Fin n2) :
    matrixInner X (coordinateMatrix i j) = X i j := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single i]
  · rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  · intro a _ ha
    refine Finset.sum_eq_zero (fun b _ => ?_)
    simp [ha]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem P.D4.MC.tangentCoordinateKernel_eq_entry {n1 n2 r : Nat} {M : RealMatrix n1 n2}
    (S : SVD M r) (a : Fin n1) (b : Fin n2) (i : Fin n1) (j : Fin n2) :
    tangentCoordinateKernel S a b i j
      = (tangentProjection S (coordinateMatrix a b)) i j := by
  unfold tangentCoordinateKernel
  rw [matrixInner_coordinateMatrix]

theorem P.D4.MC.matrixInner_le_frob {n1 n2 : Nat} (X Y : RealMatrix n1 n2) :
    |matrixInner X Y| ≤ frobeniusNorm X * frobeniusNorm Y := by

  have hinner : matrixInner X Y
      = ∑ p : Fin n1 × Fin n2, X p.1 p.2 * Y p.1 p.2 := by
    unfold matrixInner
    rw [← Finset.sum_product']; rfl
  have hX : frobeniusNormSq X = ∑ p : Fin n1 × Fin n2, (X p.1 p.2) ^ 2 := by
    unfold frobeniusNormSq
    rw [← Finset.sum_product']; rfl
  have hY : frobeniusNormSq Y = ∑ p : Fin n1 × Fin n2, (Y p.1 p.2) ^ 2 := by
    unfold frobeniusNormSq
    rw [← Finset.sum_product']; rfl

  have hcs : (matrixInner X Y) ^ 2 ≤ frobeniusNormSq X * frobeniusNormSq Y := by
    rw [hinner, hX, hY]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun p : Fin n1 × Fin n2 => X p.1 p.2) (fun p : Fin n1 × Fin n2 => Y p.1 p.2)

  have hXnn : 0 ≤ frobeniusNormSq X := by
    rw [hX]; exact Finset.sum_nonneg (fun p _ => sq_nonneg _)
  have hYnn : 0 ≤ frobeniusNormSq Y := by
    rw [hY]; exact Finset.sum_nonneg (fun p _ => sq_nonneg _)
  unfold frobeniusNorm
  rw [← Real.sqrt_mul hXnn]

  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt hcs

theorem P.D4.MC.offdiag_kernel_mag {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Cker : ℝ)
    (hdiag : ∀ a b, |tangentCoordinateKernel S a b a b| ≤ Cker) (hCker : 0 ≤ Cker)
    (hfrob : ∀ i j, frobeniusNormSq (tangentProjection S (coordinateMatrix i j))
        = tangentCoordinateKernel S i j i j)
    (i : Fin n1) (j : Fin n2) (a : Fin n1) (b : Fin n2) :
    |tangentCoordinateKernel S i j a b| ≤ Cker := by

  rw [tangentCoordinateKernel_eq_proj_inner]
  refine le_trans (matrixInner_le_frob _ _) ?_

  have key : ∀ (x : Fin n1) (y : Fin n2),
      frobeniusNorm (tangentProjection S (coordinateMatrix x y)) ≤ Real.sqrt Cker := by
    intro x y
    unfold frobeniusNorm
    rw [hfrob x y]
    refine Real.sqrt_le_sqrt ?_
    have := hdiag x y
    exact le_trans (le_abs_self _) this
  calc frobeniusNorm (tangentProjection S (coordinateMatrix i j))
          * frobeniusNorm (tangentProjection S (coordinateMatrix a b))
        ≤ Real.sqrt Cker * Real.sqrt Cker := by
          apply mul_le_mul (key i j) (key a b) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    _ = Cker := Real.mul_self_sqrt hCker

theorem P.D4.MC.base_entrysup {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (Cker : ℝ)
    (hdiag : ∀ a b, |tangentCoordinateKernel S a b a b| ≤ Cker) (hCker : 0 ≤ Cker)
    (hfrob : ∀ i j, frobeniusNormSq (tangentProjection S (coordinateMatrix i j))
        = tangentCoordinateKernel S i j i j)
    (w1 : Fin n1 × Fin n2) :
    entrySupNorm (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤ Cker ^ 2 := by
  have hCker2 : (0 : ℝ) ≤ Cker ^ 2 := sq_nonneg _

  have hentry : ∀ (i : Fin n1) (j : Fin n2),
      |quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1 i j| ≤ Cker ^ 2 := by
    intro i j
    unfold quadraticMiddleIndexDistinctKernelSquareBaseMatrix
    by_cases h : (i, j) = w1
    · simp [h, hCker2]
    · rw [if_neg h, abs_mul, sq]
      exact mul_le_mul
        (offdiag_kernel_mag S Cker hdiag hCker hfrob w1.1 w1.2 i j)
        (offdiag_kernel_mag S Cker hdiag hCker hfrob i j w1.1 w1.2)
        (abs_nonneg _) hCker

  unfold entrySupNorm
  refine Real.iSup_le (fun i => ?_) hCker2
  refine Real.iSup_le (fun j => ?_) hCker2
  exact hentry i j

theorem P.D4.MC.base_frob {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r) (Cker : ℝ)
    (hdiag : ∀ a b, |tangentCoordinateKernel S a b a b| ≤ Cker) (hCker : 0 ≤ Cker)
    (hfrob : ∀ i j, frobeniusNormSq (tangentProjection S (coordinateMatrix i j))
        = tangentCoordinateKernel S i j i j)
    (w1 : Fin n1 × Fin n2) :
    frobeniusNorm (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1)
      ≤ Real.sqrt (Cker ^ 3) := by

  have hsq : frobeniusNormSq (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1)
      ≤ Cker ^ 3 := by
    unfold frobeniusNormSq

    have hpt : ∀ (i : Fin n1) (j : Fin n2),
        (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1 i j) ^ 2
          ≤ Cker ^ 2 * (tangentCoordinateKernel S w1.1 w1.2 i j) ^ 2 := by
      intro i j
      unfold quadraticMiddleIndexDistinctKernelSquareBaseMatrix
      by_cases h : (i, j) = w1
      · rw [if_pos h, zero_pow (by norm_num)]
        positivity
      · rw [if_neg h, mul_pow]

        have hKle : (tangentCoordinateKernel S i j w1.1 w1.2) ^ 2 ≤ Cker ^ 2 := by
          have := offdiag_kernel_mag S Cker hdiag hCker hfrob i j w1.1 w1.2
          rw [← sq_abs (tangentCoordinateKernel S i j w1.1 w1.2)]
          exact pow_le_pow_left₀ (abs_nonneg _) this 2
        rw [mul_comm (tangentCoordinateKernel S w1.1 w1.2 i j ^ 2)]
        exact mul_le_mul_of_nonneg_right hKle (sq_nonneg _)

    calc (∑ i, ∑ j, (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1 i j) ^ 2)
          ≤ ∑ i, ∑ j, Cker ^ 2 * (tangentCoordinateKernel S w1.1 w1.2 i j) ^ 2 := by
            refine Finset.sum_le_sum (fun i _ => ?_)
            refine Finset.sum_le_sum (fun j _ => ?_)
            exact hpt i j
      _ = Cker ^ 2 * ∑ i, ∑ j, (tangentCoordinateKernel S w1.1 w1.2 i j) ^ 2 := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl (fun i _ => ?_)
            rw [Finset.mul_sum]
      _ = Cker ^ 2 * frobeniusNormSq (tangentProjection S (coordinateMatrix w1.1 w1.2)) := by
            congr 1
            unfold frobeniusNormSq
            refine Finset.sum_congr rfl (fun i _ => ?_)
            refine Finset.sum_congr rfl (fun j _ => ?_)

            rw [tangentCoordinateKernel_eq_entry]
      _ = Cker ^ 2 * tangentCoordinateKernel S w1.1 w1.2 w1.1 w1.2 := by
            rw [hfrob w1.1 w1.2]
      _ ≤ Cker ^ 2 * Cker := by
            refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
            exact le_trans (le_abs_self _) (hdiag w1.1 w1.2)
      _ = Cker ^ 3 := by ring

  unfold frobeniusNorm
  exact Real.sqrt_le_sqrt hsq

end

open MatrixCompletion P.D4.MC

theorem P.D4.quadratic_neumann_middle_index_distinct_kernel_square_base_entry_sup_norm_bound_min_dim :
    ∃ Centry : ℝ, 0 < Centry ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ w1 : Fin n₁ × Fin n₂,
          entrySupNorm (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
            Centry * μ₀ ^ 2 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 2) := by
  obtain ⟨Cker, hCkerpos, hbrick⟩ :=
    tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim
  refine ⟨Cker ^ 2, by positivity, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 w1
  set D : ℝ := Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) with hD
  have hμ₀pos : (0 : ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hDnn : 0 ≤ D := by
    rw [hD]
    have h1 : 0 ≤ Cker * μ₀ := mul_nonneg (le_of_lt hCkerpos) (le_of_lt hμ₀pos)
    apply mul_nonneg h1
    exact div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg _)
  have hdiag : ∀ (x : Fin n₁) (y : Fin n₂),
      |tangentCoordinateKernel S x y x y| ≤ D := by
    intro x y; rw [hD]; exact hbrick n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 x y
  have hfrob : ∀ (x : Fin n₁) (y : Fin n₂),
      frobeniusNormSq (tangentProjection S (coordinateMatrix x y))
        = tangentCoordinateKernel S x y x y := by
    intro x y
    rw [tangentCoordinateKernel_eq_proj_inner S x y x y]
    unfold frobeniusNormSq matrixInner
    exact Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => by rw [sq]))

  have hbase := base_entrysup S D hdiag hDnn hfrob w1
  have heq : D ^ 2 = Cker ^ 2 * μ₀ ^ 2 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 2) := by
    rw [hD]; ring
  rw [heq] at hbase
  exact hbase
end
export P.D4 (quadratic_neumann_middle_index_distinct_kernel_square_base_entry_sup_norm_bound_min_dim)

section
open MatrixCompletion
open scoped BigOperators

open MatrixCompletion P.D4.MC

theorem P.D5.quadratic_neumann_middle_index_distinct_kernel_square_base_frobenius_norm_bound_min_dim :
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
        ∀ w1 : Fin n₁ × Fin n₂,
          frobeniusNorm (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) ≤
            Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
              Real.rpow ((r : ℝ) / (↑(min n₁ n₂))) ((3 : ℝ) / 2) := by
  obtain ⟨Cker, hCkerpos, hbrick⟩ :=
    tangent_coordinate_kernel_diagonal_bound_from_a0_min_dim
  refine ⟨Real.sqrt (Cker ^ 3), Real.sqrt_pos.mpr (by positivity), ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 w1
  set D : ℝ := Cker * μ₀ * ((r : ℝ) / (↑(min n₁ n₂))) with hD
  have hμ₀pos : (0 : ℝ) < μ₀ := lt_of_lt_of_le one_pos hμ₀
  have hμ₀nn : (0 : ℝ) ≤ μ₀ := le_of_lt hμ₀pos
  have hrm_nn : (0 : ℝ) ≤ (r : ℝ) / (↑(min n₁ n₂)) :=
    div_nonneg (Nat.cast_nonneg r) (Nat.cast_nonneg _)
  have hDnn : 0 ≤ D := by
    rw [hD]; exact mul_nonneg (mul_nonneg (le_of_lt hCkerpos) hμ₀nn) hrm_nn
  have hdiag : ∀ (x : Fin n₁) (y : Fin n₂),
      |tangentCoordinateKernel S x y x y| ≤ D := by
    intro x y; rw [hD]; exact hbrick n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 x y
  have hfrob : ∀ (x : Fin n₁) (y : Fin n₂),
      frobeniusNormSq (tangentProjection S (coordinateMatrix x y))
        = tangentCoordinateKernel S x y x y := by
    intro x y
    rw [tangentCoordinateKernel_eq_proj_inner S x y x y]
    unfold frobeniusNormSq matrixInner
    exact Finset.sum_congr rfl (fun p _ =>
      Finset.sum_congr rfl (fun q _ => by rw [sq]))
  have hbase := base_frob S D hdiag hDnn hfrob w1

  have sqrt_cube : ∀ x : ℝ, 0 ≤ x →
      Real.sqrt (x ^ 3) = Real.rpow x ((3 : ℝ) / 2) := by
    intro x hx
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 3, ← Real.rpow_mul hx]
    norm_num
  have hsplit : Real.sqrt (D ^ 3) =
      Real.sqrt (Cker ^ 3) * Real.rpow μ₀ ((3 : ℝ) / 2) *
        Real.rpow ((r : ℝ) / (↑(min n₁ n₂))) ((3 : ℝ) / 2) := by
    have hcube : D ^ 3 = Cker ^ 3 * (μ₀ ^ 3 * ((r : ℝ) / (↑(min n₁ n₂))) ^ 3) := by
      rw [hD]; ring
    rw [hcube, Real.sqrt_mul (by positivity),
        Real.sqrt_mul (by positivity)]
    rw [sqrt_cube μ₀ hμ₀nn, sqrt_cube _ hrm_nn]
    ring
  rw [hsplit] at hbase
  exact hbase
end
export P.D5 (quadratic_neumann_middle_index_distinct_kernel_square_base_frobenius_norm_bound_min_dim)

section
open MatrixCompletion
open scoped Classical BigOperators

private theorem P.D6.csf_apply {n₁ n₂ : Nat} (Omega : Finset (Fin n₁ × Fin n₂)) (p : ℝ)
    (X : Matrix (Fin n₁) (Fin n₂) ℝ) (i : Fin n₁) (j : Fin n₂) :
    centeredSamplingFluctuation Omega p X i j
      = p⁻¹ * (centeredIndicator Omega p i j * X i j) := by
  show (p⁻¹ • (samplingProjection Omega X - p • X)) i j = _
  simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
  unfold samplingProjection centeredIndicator
  by_cases hm : (i, j) ∈ Omega
  · rw [if_pos hm, if_pos hm]; ring
  · rw [if_neg hm, if_neg hm]; ring

theorem P.D6.quadratic_neumann_middle_index_distinct_mean_coefficient_as_centered_scalar_fluctuation
    {n₁ n₂ r : Nat} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r)
    (p : ℝ) (w1 : Fin n₁ × Fin n₂) :
    quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1 =
      matrixEntrySum
        (centeredSamplingFluctuation Omega p
          (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1)) := by
  unfold quadraticMiddleIndexDistinctMeanCoefficient matrixEntrySum
  simp only [csf_apply, quadraticMiddleIndexDistinctKernelSquareBaseMatrix, Prod.mk.eta]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  by_cases h : w = w1
  · simp [h]
  · rw [if_neg h, if_neg h]; ring
end
export P.D6 (quadratic_neumann_middle_index_distinct_mean_coefficient_as_centered_scalar_fluctuation)

section
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

theorem P.D7.bernoulli_powerset_expectation_prod_factor {n₁ n₂ : ℕ} (p : ℝ)
    (f : (Fin n₁ × Fin n₂) → ℝ → ℝ) :
    bernoulliExpectation p
        (fun Omega => ∏ w : Fin n₁ × Fin n₂, f w (if w ∈ Omega then 1 else 0)) =
      ∏ w : Fin n₁ × Fin n₂, (p * f w 1 + (1 - p) * f w 0) := by
  classical
  have hpa := Finset.prod_add (fun w : Fin n₁ × Fin n₂ => p * f w 1)
    (fun w => (1 - p) * f w 0) Finset.univ
  rw [hpa, Finset.powerset_univ]
  unfold bernoulliExpectation bernoulliObservationWeight
  apply Finset.sum_congr rfl
  intro t _
  simp only []
  have hsplit :
      (∏ w : Fin n₁ × Fin n₂, f w (if w ∈ t then 1 else 0)) =
        (∏ w ∈ t, f w 1) * ∏ w ∈ Finset.univ \ t, f w 0 := by
    rw [← Finset.prod_mul_prod_compl t (fun w => f w (if w ∈ t then 1 else 0)),
        Finset.compl_eq_univ_sdiff]
    congr 1
    · apply Finset.prod_congr rfl; intro w hw; simp [hw]
    · apply Finset.prod_congr rfl; intro w hw
      simp only [Finset.mem_sdiff] at hw; simp [hw.2]
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
      Finset.prod_const, Finset.prod_const, hsplit]
  rw [Finset.card_univ_diff]; ring
end
export P.D7 (bernoulli_powerset_expectation_prod_factor)

section
open MatrixCompletion
open scoped BigOperators Classical

theorem P.D8.centered_sampling_coefficient_mgf_factorization {n₁ n₂ : ℕ}
    (p : ℝ) (B : Matrix (Fin n₁) (Fin n₂) ℝ) (lam : ℝ) :
    bernoulliExpectation p
        (fun Omega =>
          Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Omega p B))) =
      ∏ w : Fin n₁ × Fin n₂,
        (p * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
          + (1 - p) * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))) := by
  classical
  set f : (Fin n₁ × Fin n₂) → ℝ → ℝ :=
    fun w x => Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (x - p))) with hf
  have key := bernoulli_powerset_expectation_prod_factor (n₁ := n₁) (n₂ := n₂) p f
  have hL : (fun Omega : Finset (Fin n₁ × Fin n₂) =>
        ∏ w : Fin n₁ × Fin n₂, f w (if w ∈ Omega then 1 else 0)) =
      (fun Omega =>
        Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Omega p B))) := by
    funext Omega
    have hcoeff : matrixEntrySum (centeredSamplingFluctuation Omega p B) =
        ∑ w : Fin n₁ × Fin n₂,
          (p⁻¹ * (B w.1 w.2) * ((if w ∈ Omega then 1 else 0) - p)) := by
      unfold matrixEntrySum centeredSamplingFluctuation
      apply Finset.sum_congr rfl
      intro w _
      simp only [Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      unfold samplingProjection
      by_cases h : (w.1, w.2) ∈ Omega
      · simp only [h, if_true]; ring
      · simp only [h, if_false]; ring
    rw [hcoeff, Finset.mul_sum, Real.exp_sum]
  rw [hL] at key
  rw [key]
end
export P.D8 (centered_sampling_coefficient_mgf_factorization)

section
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem P.D9.exp_le_quad (x : ℝ) (hx : x ≤ 1) : Real.exp x ≤ 1 + x + x^2 := by
  set phi : ℝ → ℝ := fun t => Real.exp (-t) * (1 + t + t^2) with hphi
  have hderiv : ∀ t : ℝ, HasDerivAt phi (Real.exp (-t) * (t * (1 - t))) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Real.exp (-t)) (-Real.exp (-t)) t :=
      (hasDerivAt_neg t).exp.congr_deriv (by ring)
    have h2 : HasDerivAt (fun t : ℝ => 1 + t + t^2) (1 + 2*t) t :=
      (((hasDerivAt_id t).const_add 1).add (hasDerivAt_pow 2 t)).congr_deriv (by norm_num)
    rw [hphi]
    exact (h1.mul h2).congr_deriv (by ring)
  have hphi0 : phi 0 = 1 := by simp [hphi]
  have hge : 1 ≤ phi x := by
    rcases lt_or_ge x 0 with hx0 | hx0
    ·
      have hanti : AntitoneOn phi (Set.Iic 0) := by
        apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
        · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
        · intro t _; exact (hderiv t).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [(hderiv t).deriv]
          rw [interior_Iic] at ht
          have ht0 : t < 0 := ht
          have hneg : t * (1 - t) ≤ 0 := by nlinarith [ht0]
          have hexp : 0 < Real.exp (-t) := Real.exp_pos _
          nlinarith [mul_nonneg hexp.le (neg_nonneg.mpr hneg)]
      have := hanti (Set.mem_Iic.mpr (le_of_lt hx0)) (Set.mem_Iic.mpr le_rfl) (le_of_lt hx0)
      rwa [hphi0] at this
    ·
      have hmono : MonotoneOn phi (Set.Icc 0 1) := by
        apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
        · exact fun t _ => (hderiv t).continuousAt.continuousWithinAt
        · intro t _; exact (hderiv t).differentiableAt.differentiableWithinAt
        · intro t ht
          rw [(hderiv t).deriv]
          rw [interior_Icc] at ht
          have ht0 : 0 < t := ht.1
          have ht1 : t < 1 := ht.2
          have hge0 : 0 ≤ t * (1 - t) := by nlinarith [ht0, ht1]
          have hexp : 0 < Real.exp (-t) := Real.exp_pos _
          positivity
      have := hmono (Set.mem_Icc.mpr ⟨le_refl 0, by norm_num⟩) (Set.mem_Icc.mpr ⟨hx0, hx⟩) hx0
      rwa [hphi0] at this
  have hexp : 0 < Real.exp x := Real.exp_pos x
  have hge' : 1 ≤ Real.exp (-x) * (1 + x + x^2) := hge
  rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ hexp] at hge'
  linarith [hge']
end
export P.D9 (exp_le_quad)

section
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem P.D10.two_point_bernstein_mgf (p a b : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcent : p * a + (1 - p) * b = 0) (ha : a ≤ 1) (hb : b ≤ 1) :
    p * Real.exp a + (1 - p) * Real.exp b ≤
      Real.exp (p * a^2 + (1 - p) * b^2) := by
  have hEa := exp_le_quad a ha
  have hEb := exp_le_quad b hb
  have h1p : (0:ℝ) ≤ 1 - p := by linarith
  have hV : (0:ℝ) ≤ p * a^2 + (1 - p) * b^2 := by positivity

  have hcomb : p * Real.exp a + (1 - p) * Real.exp b ≤ 1 + (p*a^2 + (1-p)*b^2) := by
    have h := add_le_add (mul_le_mul_of_nonneg_left hEa hp0)
                         (mul_le_mul_of_nonneg_left hEb h1p)
    nlinarith [h, hcent]

  have hexpV : 1 + (p*a^2 + (1-p)*b^2) ≤ Real.exp (p*a^2 + (1-p)*b^2) := by
    have := Real.add_one_le_exp (p*a^2 + (1-p)*b^2); linarith
  linarith [hcomb, hexpV]
end
export P.D10 (two_point_bernstein_mgf)

section
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1000000

theorem P.D11.centered_sampling_coefficient_bernstein_mgf {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (B : Matrix (Fin n₁) (Fin n₂) ℝ) (entryScale lam : ℝ)
    (hent : entrySupNorm B ≤ entryScale) (hes : 0 < entryScale)
    (hlam0 : 0 ≤ lam) (hlam : lam ≤ p / entryScale) :
    bernoulliExpectation p
        (fun Omega =>
          Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Omega p B))) ≤
      Real.exp (lam ^ 2 * ((1 - p) / p) * frobeniusNormSq B) := by
  classical
  have hpne : p ≠ 0 := ne_of_gt hp0

  have hBw : ∀ w : Fin n₁ × Fin n₂, |B w.1 w.2| ≤ entryScale := by
    intro w
    refine le_trans ?_ hent
    have hbdd2 : ∀ i : Fin n₁, BddAbove (Set.range (fun j : Fin n₂ => |B i j|)) :=
      fun i => Set.Finite.bddAbove (Set.finite_range _)
    have hbdd1 : BddAbove (Set.range (fun i : Fin n₁ => ⨆ j : Fin n₂, |B i j|)) :=
      Set.Finite.bddAbove (Set.finite_range _)
    unfold entrySupNorm
    refine le_trans (le_ciSup (hbdd2 w.1) w.2) ?_
    exact le_ciSup hbdd1 w.1

  have hkey : ∀ w : Fin n₁ × Fin n₂, lam * |B w.1 w.2| / p ≤ 1 := by
    intro w
    rw [div_le_one hp0]

    have h1 : lam * |B w.1 w.2| ≤ lam * entryScale :=
      mul_le_mul_of_nonneg_left (hBw w) hlam0
    have h2 : lam * entryScale ≤ p := by
      rw [le_div_iff₀ hes] at hlam; linarith [hlam]
    linarith
  rw [centered_sampling_coefficient_mgf_factorization p B lam]

  have hfac : ∀ w : Fin n₁ × Fin n₂,
      (p * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
        + (1 - p) * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))) ≤
      Real.exp (lam ^ 2 * ((1 - p) / p) * (B w.1 w.2) ^ 2) := by
    intro w

    have h1p : (0:ℝ) ≤ 1 - p := by linarith
    have hkw := hkey w

    have hcent : p * (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
        + (1 - p) * (lam * (p⁻¹ * (B w.1 w.2) * (0 - p))) = 0 := by
      field_simp; ring

    have ha1 : lam * (p⁻¹ * (B w.1 w.2) * (1 - p)) ≤ 1 := by
      have hle : (B w.1 w.2) * (1 - p) ≤ |B w.1 w.2| := by
        calc (B w.1 w.2) * (1 - p) ≤ |B w.1 w.2| * (1 - p) :=
              mul_le_mul_of_nonneg_right (le_abs_self _) h1p
          _ ≤ |B w.1 w.2| * 1 := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
          _ = |B w.1 w.2| := by ring
      have hstep : lam * (p⁻¹ * (B w.1 w.2) * (1 - p)) ≤ lam * |B w.1 w.2| / p := by
        calc lam * (p⁻¹ * (B w.1 w.2) * (1 - p))
            = lam * p⁻¹ * ((B w.1 w.2) * (1 - p)) := by ring
          _ ≤ lam * p⁻¹ * |B w.1 w.2| := mul_le_mul_of_nonneg_left hle (by positivity)
          _ = lam * |B w.1 w.2| / p := by rw [mul_comm lam (p⁻¹), mul_assoc, mul_comm (p⁻¹) (lam * |B w.1 w.2|), div_eq_mul_inv]
      linarith [hstep, hkw]

    have hb1 : lam * (p⁻¹ * (B w.1 w.2) * (0 - p)) ≤ 1 := by
      have hle : (B w.1 w.2) * (0 - p) ≤ |B w.1 w.2| := by
        calc (B w.1 w.2) * (0 - p) = -(B w.1 w.2) * p := by ring
          _ ≤ |B w.1 w.2| * p := mul_le_mul_of_nonneg_right (neg_le_abs _) (le_of_lt hp0)
          _ ≤ |B w.1 w.2| * 1 := mul_le_mul_of_nonneg_left hp1 (abs_nonneg _)
          _ = |B w.1 w.2| := by ring
      have hstep : lam * (p⁻¹ * (B w.1 w.2) * (0 - p)) ≤ lam * |B w.1 w.2| / p := by
        calc lam * (p⁻¹ * (B w.1 w.2) * (0 - p))
            = lam * p⁻¹ * ((B w.1 w.2) * (0 - p)) := by ring
          _ ≤ lam * p⁻¹ * |B w.1 w.2| := mul_le_mul_of_nonneg_left hle (by positivity)
          _ = lam * |B w.1 w.2| / p := by rw [mul_comm lam (p⁻¹), mul_assoc, mul_comm (p⁻¹) (lam * |B w.1 w.2|), div_eq_mul_inv]
      linarith [hstep, hkw]
    have hH := two_point_bernstein_mgf p
      (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
      (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))
      (le_of_lt hp0) hp1 hcent ha1 hb1
    refine hH.trans ?_
    apply Real.exp_le_exp.mpr
    apply le_of_eq
    field_simp; ring
  calc ∏ w : Fin n₁ × Fin n₂,
        (p * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))
          + (1 - p) * Real.exp (lam * (p⁻¹ * (B w.1 w.2) * (0 - p))))
      ≤ ∏ w : Fin n₁ × Fin n₂, Real.exp (lam ^ 2 * ((1 - p) / p) * (B w.1 w.2) ^ 2) := by
        apply Finset.prod_le_prod
        · intro w _
          have h1p : (0:ℝ) ≤ 1 - p := by linarith
          have e1 := mul_nonneg (le_of_lt hp0) (Real.exp_pos (lam * (p⁻¹ * (B w.1 w.2) * (1 - p)))).le
          have e2 := mul_nonneg h1p (Real.exp_pos (lam * (p⁻¹ * (B w.1 w.2) * (0 - p)))).le
          linarith
        · intro w _; exact hfac w
    _ = Real.exp (∑ w : Fin n₁ × Fin n₂, lam ^ 2 * ((1 - p) / p) * (B w.1 w.2) ^ 2) := by
        rw [← Real.exp_sum]
    _ = Real.exp (lam ^ 2 * ((1 - p) / p) * frobeniusNormSq B) := by
        congr 1
        rw [frobeniusNormSq, ← Fintype.sum_prod_type']
        rw [Finset.mul_sum]
end
export P.D11 (centered_sampling_coefficient_bernstein_mgf)

section
set_option maxHeartbeats 1000000
open scoped BigOperators

theorem P.D12.rpow_mul_exp_neg_le (q lam x : ℝ) (hq : 0 < q) (hlam : 0 < lam) (hx : 0 ≤ x) :
    x ^ q * Real.exp (-(lam * x)) ≤ (q / (lam * Real.exp 1)) ^ q := by

  rcases eq_or_lt_of_le hx with hx0 | hxpos
  ·
    rw [← hx0]
    rw [Real.zero_rpow (ne_of_gt hq)]
    simp only [zero_mul]
    positivity
  ·
    have hRpos : 0 < q / (lam * Real.exp 1) := by positivity
    have hLpos : 0 < x ^ q * Real.exp (-(lam * x)) := by
      have := Real.rpow_pos_of_pos hxpos q
      positivity
    rw [← Real.log_le_log_iff hLpos (Real.rpow_pos_of_pos hRpos q)]

    rw [Real.log_mul (ne_of_gt (Real.rpow_pos_of_pos hxpos q)) (ne_of_gt (Real.exp_pos _))]
    rw [Real.log_rpow hxpos, Real.log_exp, Real.log_rpow hRpos]

    have hlogR : Real.log (q / (lam * Real.exp 1)) = Real.log q - Real.log lam - 1 := by
      rw [Real.log_div (ne_of_gt hq) (by positivity),
          Real.log_mul (ne_of_gt hlam) (ne_of_gt (Real.exp_pos 1)), Real.log_exp]
      ring
    rw [hlogR]

    set u := lam * x / q with hu
    have hupos : 0 < u := by rw [hu]; positivity
    have hlogu : Real.log u ≤ u - 1 := Real.log_le_sub_one_of_pos hupos

    have hlu : Real.log u = Real.log lam + Real.log x - Real.log q := by
      rw [hu, Real.log_div (by positivity) (ne_of_gt hq),
          Real.log_mul (ne_of_gt hlam) (ne_of_gt hxpos)]
    rw [hlu] at hlogu

    have := mul_le_mul_of_nonneg_left hlogu (le_of_lt hq)

    have hrhs : q * (lam * x / q - 1) = lam * x - q := by field_simp
    rw [hrhs] at this
    nlinarith [this]
end
export P.D12 (rpow_mul_exp_neg_le)

section
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1000000

theorem P.D13.bernoulli_moment_from_two_sided_mgf {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (lam M q : ℝ)
    (hlam : 0 < lam) (hq : 0 < q)
    (hMGFpos : bernoulliExpectation p (fun Omega => Real.exp (lam * Z Omega)) ≤ M)
    (hMGFneg : bernoulliExpectation p (fun Omega => Real.exp (-(lam * Z Omega))) ≤ M) :
    bernoulliExpectation p (fun Omega => |Z Omega| ^ q) ≤
      2 * (q / (lam * Real.exp 1)) ^ q * M := by
  classical

  have hpoint : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      |Z Omega| ^ q ≤ (q / (lam * Real.exp 1)) ^ q *
        (Real.exp (lam * Z Omega) + Real.exp (-(lam * Z Omega))) := by
    intro Om

    have hx : (0:ℝ) ≤ |Z Om| := abs_nonneg _
    have hbase := rpow_mul_exp_neg_le q lam (|Z Om|) hq hlam hx
    have hepos : (0:ℝ) < Real.exp (-(lam * |Z Om|)) := Real.exp_pos _

    have hstep : |Z Om| ^ q ≤ (q / (lam * Real.exp 1)) ^ q * Real.exp (lam * |Z Om|) := by
      have hle : |Z Om| ^ q ≤ (q / (lam * Real.exp 1)) ^ q / Real.exp (-(lam * |Z Om|)) :=
        (le_div_iff₀ hepos).mpr hbase
      calc |Z Om| ^ q ≤ (q / (lam * Real.exp 1)) ^ q / Real.exp (-(lam * |Z Om|)) := hle
        _ = (q / (lam * Real.exp 1)) ^ q * Real.exp (lam * |Z Om|) := by
            rw [Real.exp_neg, div_inv_eq_mul]

    have hexpabs : Real.exp (lam * |Z Om|) ≤ Real.exp (lam * Z Om) + Real.exp (-(lam * Z Om)) := by
      rcases abs_cases (Z Om) with ⟨he, _⟩ | ⟨he, _⟩
      · rw [he]
        have : (0:ℝ) ≤ Real.exp (-(lam * Z Om)) := (Real.exp_pos _).le
        linarith
      · rw [he]
        have hpos : (0:ℝ) ≤ Real.exp (lam * Z Om) := (Real.exp_pos _).le
        have : lam * -(Z Om) = -(lam * Z Om) := by ring
        rw [this]; linarith
    calc |Z Om| ^ q ≤ (q / (lam * Real.exp 1)) ^ q * Real.exp (lam * |Z Om|) := hstep
      _ ≤ (q / (lam * Real.exp 1)) ^ q *
            (Real.exp (lam * Z Om) + Real.exp (-(lam * Z Om))) := by
          apply mul_le_mul_of_nonneg_left hexpabs (by positivity)

  unfold bernoulliExpectation
  have hwnn : ∀ Om : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Om := by
    intro Om; unfold bernoulliObservationWeight
    have : (0:ℝ) ≤ 1 - p := by linarith
    positivity

  calc ∑ Om : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Om * |Z Om| ^ q
      ≤ ∑ Om : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Om *
          ((q / (lam * Real.exp 1)) ^ q *
            (Real.exp (lam * Z Om) + Real.exp (-(lam * Z Om)))) := by
        apply Finset.sum_le_sum
        intro Om _
        exact mul_le_mul_of_nonneg_left (hpoint Om) (hwnn Om)
    _ = (q / (lam * Real.exp 1)) ^ q *
          ((∑ Om : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Om * Real.exp (lam * Z Om))
           + (∑ Om : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Om * Real.exp (-(lam * Z Om)))) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro Om _; ring
    _ ≤ (q / (lam * Real.exp 1)) ^ q * (M + M) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact add_le_add hMGFpos hMGFneg
    _ = 2 * (q / (lam * Real.exp 1)) ^ q * M := by ring
end
export P.D13 (bernoulli_moment_from_two_sided_mgf)

section
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1600000

section

variable {n₁ n₂ : ℕ}

theorem P.D14.ProveAA.coeff_neg (p : ℝ) (B : Matrix (Fin n₁) (Fin n₂) ℝ)
    (Om : Finset (Fin n₁ × Fin n₂)) :
    matrixEntrySum (centeredSamplingFluctuation Om p (-B)) =
      -(matrixEntrySum (centeredSamplingFluctuation Om p B)) := by
  unfold matrixEntrySum
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro w _
  show p⁻¹ * ((samplingProjection Om (-B)) w.1 w.2 - p * (-B) w.1 w.2)
      = -(p⁻¹ * ((samplingProjection Om B) w.1 w.2 - p * B w.1 w.2))
  by_cases h : (w.1, w.2) ∈ Om <;>
    simp [samplingProjection, Matrix.neg_apply, h] <;> ring

theorem P.D14.ProveAA.entrySup_neg (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    entrySupNorm (-B) = entrySupNorm B := by
  unfold entrySupNorm; simp only [Matrix.neg_apply, abs_neg]

theorem P.D14.ProveAA.frobSq_neg (B : Matrix (Fin n₁) (Fin n₂) ℝ) :
    frobeniusNormSq (-B) = frobeniusNormSq B := by
  unfold frobeniusNormSq
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [Matrix.neg_apply]; ring

theorem P.D14.ProveAA.bound_step (q p V E frob : ℝ) (hq : 1 ≤ q) (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hV : 0 < V) (hE : 0 < E) (hfrob : 0 ≤ frob) (hVfrob : V ≤ frob^2 / p) :
    2 * (q / (Real.exp 1 * (min (Real.sqrt (q/(2*V)) ) (p/E)))) ^ q
        * Real.exp (min (Real.sqrt (q/(2*V))) (p/E)^2 * V) ≤
      (2 * Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q := by
  set lam := min (Real.sqrt (q/(2*V))) (p/E) with hlamdef
  have hqpos : 0 < q := lt_of_lt_of_le one_pos hq
  have hsqrtpos : 0 < Real.sqrt (q/(2*V)) := Real.sqrt_pos.mpr (by positivity)
  have hpEpos : 0 < p/E := by positivity
  have hlampos : 0 < lam := lt_min hsqrtpos hpEpos
  have hlamA : lam ≤ Real.sqrt (q/(2*V)) := min_le_left _ _
  have hlamB : lam ≤ p/E := min_le_right _ _
  have hlam2V : lam^2 * V ≤ q/2 := by
    have h1 : lam^2 ≤ q/(2*V) := by
      have hh := Real.sq_sqrt (show (0:ℝ) ≤ q/(2*V) by positivity)
      nlinarith [hlamA, hlampos, Real.sqrt_nonneg (q/(2*V)), hh,
        mul_le_mul hlamA hlamA hlampos.le (Real.sqrt_nonneg _)]
    have heq : (q/(2*V)) * V = q/2 := by
      rw [div_mul_eq_mul_div, mul_comm 2 V, ← div_div, mul_div_assoc, div_self (ne_of_gt hV), mul_one]
    have : lam^2 * V ≤ (q/(2*V)) * V := mul_le_mul_of_nonneg_right h1 hV.le
    rw [heq] at this; linarith [this]
  have hexp : Real.exp (lam^2 * V) ≤ Real.exp (q/2) := Real.exp_le_exp.mpr hlam2V

  have hqlam : q / lam ≤ Real.sqrt (2*V*q) + (q/p) * E := by
    rw [div_le_iff₀ hlampos]
    rcases le_total (Real.sqrt (q/(2*V))) (p/E) with hcase | hcase
    · have hl : lam = Real.sqrt (q/(2*V)) := by rw [hlamdef, min_eq_left hcase]
      rw [hl]
      have hsq : Real.sqrt (2*V*q) * Real.sqrt (q/(2*V)) = q := by
        rw [← Real.sqrt_mul (by positivity)]
        rw [show (2*V*q) * (q/(2*V)) = q^2 by field_simp]
        rw [Real.sqrt_sq hqpos.le]
      have hrest : 0 ≤ (q/p) * E * Real.sqrt (q/(2*V)) := by positivity
      nlinarith [hsq, hrest]
    · have hl : lam = p/E := by rw [hlamdef, min_eq_right hcase]
      rw [hl]
      have hqpE : (q/p) * E * (p/E) = q := by field_simp
      have hrest : 0 ≤ Real.sqrt (2*V*q) * (p/E) := by positivity
      nlinarith [hqpE, hrest]
  have hsqrt2Vq : Real.sqrt (2*V*q) ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob) := by
    have hrw : Real.sqrt 2 * (Real.sqrt (q/p) * frob) = Real.sqrt (2 * (q/p) * frob^2) := by
      rw [show (2 * (q/p) * frob^2) = 2 * ((q/p) * frob^2) by ring]
      rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
      rw [Real.sqrt_mul (div_nonneg hqpos.le hp0.le), Real.sqrt_sq hfrob]
    rw [hrw]
    apply Real.sqrt_le_sqrt
    have hVq : V * q ≤ (frob^2/p) * q := mul_le_mul_of_nonneg_right hVfrob hqpos.le
    have : (frob^2/p) * q = 2 * (q/p) * frob^2 / 2 := by ring
    nlinarith [hVq, hqpos]
  have hJ : q / lam ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob) + (q/p) * E := by
    linarith [hqlam, hsqrt2Vq]

  have hmerge : (q / (Real.exp 1 * lam)) ^ q * Real.exp (q/2)
      = (q / (lam * Real.exp (1/2))) ^ q := by
    have he2 : Real.exp (q/2) = (Real.exp (1/2)) ^ q := by rw [← Real.exp_mul]; ring_nf
    rw [he2, ← Real.mul_rpow (by positivity) (by positivity)]
    congr 1
    have hexp1 : Real.exp 1 = Real.exp (1/2) * Real.exp (1/2) := by rw [← Real.exp_add]; norm_num
    rw [hexp1]; field_simp

  have hstep1 : 2 * (q / (Real.exp 1 * lam)) ^ q * Real.exp (lam^2 * V)
      ≤ 2 * (q / (lam * Real.exp (1/2))) ^ q := by
    have h := mul_le_mul_of_nonneg_left hexp
      (show (0:ℝ) ≤ 2 * (q / (Real.exp 1 * lam)) ^ q by positivity)
    calc 2 * (q / (Real.exp 1 * lam)) ^ q * Real.exp (lam^2 * V)
        = (2 * (q / (Real.exp 1 * lam)) ^ q) * Real.exp (lam^2 * V) := by ring
      _ ≤ (2 * (q / (Real.exp 1 * lam)) ^ q) * Real.exp (q/2) := h
      _ = 2 * ((q / (Real.exp 1 * lam)) ^ q * Real.exp (q/2)) := by ring
      _ = 2 * (q / (lam * Real.exp (1/2))) ^ q := by rw [hmerge]

  have hbase : q / (lam * Real.exp (1/2)) ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E) := by
    have hexphalf : (1:ℝ) ≤ Real.exp (1/2) := Real.one_le_exp (by norm_num)
    have h1 : q / (lam * Real.exp (1/2)) ≤ q / lam := by
      rw [div_le_div_iff₀ (by positivity) hlampos]
      have : lam ≤ lam * Real.exp (1/2) := by nlinarith [hlampos, hexphalf]
      nlinarith [hqpos, hlampos, this]
    have hJ' : q / lam ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E) := by
      have hsqrt2 : (1:ℝ) ≤ Real.sqrt 2 := by
        rw [show (1:ℝ) = Real.sqrt 1 by simp]; exact Real.sqrt_le_sqrt (by norm_num)
      have hnn : 0 ≤ (q/p) * E := by positivity
      calc q / lam ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob) + (q/p) * E := hJ
        _ ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob) + Real.sqrt 2 * ((q/p) * E) := by nlinarith [hsqrt2, hnn]
        _ = Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E) := by ring
    linarith [h1, hJ']

  have hJnn : 0 ≤ Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E) := by positivity
  have hpow : (q / (lam * Real.exp (1/2))) ^ q ≤ (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q :=
    Real.rpow_le_rpow (by positivity) hbase hqpos.le

  have hfinal : 2 * (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q
      ≤ (2 * Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q := by
    rw [show (2 * Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E))
          = 2 * (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) by ring]
    rw [Real.mul_rpow (by norm_num) hJnn]
    have h2q : (2:ℝ) ≤ 2 ^ q := by
      calc (2:ℝ) = 2 ^ (1:ℝ) := by rw [Real.rpow_one]
        _ ≤ 2 ^ q := Real.rpow_le_rpow_left_iff (by norm_num) |>.mpr hq
    have hbasenn : 0 ≤ (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q :=
      Real.rpow_nonneg hJnn q
    nlinarith [h2q, hbasenn]
  calc 2 * (q / (Real.exp 1 * lam)) ^ q * Real.exp (lam^2 * V)
      ≤ 2 * (q / (lam * Real.exp (1/2))) ^ q := hstep1
    _ ≤ 2 * (Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q := by
        apply mul_le_mul_of_nonneg_left hpow (by norm_num)
    _ ≤ (2 * Real.sqrt 2 * (Real.sqrt (q/p) * frob + (q/p) * E)) ^ q := hfinal

end

open P.D14.ProveAA

set_option maxHeartbeats 1600000

theorem P.D14.scalar_centered_sampling_qnorm_rosenthal_estimate :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
        (B : Matrix (Fin n₁) (Fin n₂) ℝ)
        (entryScale frobScale : ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤ entryScale →
        frobeniusNorm B ≤ frobScale →
        ∀ q : ℕ, 1 ≤ q →
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega => |Coeff Omega| ^ q) ≤
            (C *
                (Real.sqrt
                    ((q : ℝ) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  frobScale +
                  ((q : ℝ) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entryScale)) ^ q := by
  refine ⟨2 * Real.sqrt 2, by positivity, ?_⟩
  intro n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hent hfrob q hq1
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hnn : (0:ℝ) < (n₁:ℝ) * (n₂:ℝ) := by positivity
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hnn]; exact_mod_cast hmle
  have hentSnn : 0 ≤ entrySupNorm B := by
    unfold entrySupNorm
    refine Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))
  have hentS : 0 ≤ entryScale := le_trans hentSnn hent
  have hfrobS : 0 ≤ frobScale := le_trans (by unfold frobeniusNorm; positivity) hfrob

  have hqR : (0:ℝ) < (q:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hq1

  have hmomeq : bernoulliExpectation p (fun Omega => |Coeff Omega| ^ q)
      = bernoulliExpectation p (fun Omega =>
          |matrixEntrySum (centeredSamplingFluctuation Omega p B)| ^ q) := by
    unfold bernoulliExpectation
    apply Finset.sum_congr rfl; intro Om _; simp only []; rw [hCoeff Om]
  rw [hmomeq]

  set Z : Finset (Fin n₁ × Fin n₂) → ℝ :=
    fun Om => matrixEntrySum (centeredSamplingFluctuation Om p B) with hZ

  have hRHSnn : (0:ℝ) ≤ 2 * Real.sqrt 2 *
      (Real.sqrt ((q:ℝ)/p) * frobScale + ((q:ℝ)/p) * entryScale) := by positivity

  by_cases hdeg : p = 0 ∨ p = 1 ∨ frobeniusNormSq B = 0 ∨ entryScale = 0
  ·
    have hmom0 : bernoulliExpectation p (fun Om => |Z Om| ^ q) = 0 := by
      rcases hdeg with h | h | h | h
      ·
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Om _ => ?_)
        have hz : Z Om = 0 := by
          rw [hZ, h]; unfold matrixEntrySum centeredSamplingFluctuation; simp [inv_zero]
        simp only [hz, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
      ·
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Om _ => ?_)
        by_cases huniv : Om = Finset.univ
        · have hZ0 : Z Om = 0 := by
            rw [hZ, h, huniv]
            unfold matrixEntrySum
            refine Finset.sum_eq_zero (fun w _ => ?_)
            show (1:ℝ)⁻¹ *
                ((samplingProjection Finset.univ B) w.1 w.2 - (1:ℝ) * B w.1 w.2) = 0
            simp [samplingProjection]
          simp only [hZ0, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
        · have hw : bernoulliObservationWeight p Om = 0 := by
            rw [h]; unfold bernoulliObservationWeight
            have hcard : Om.card < Fintype.card (Fin n₁ × Fin n₂) := by
              rcases lt_or_eq_of_le (Finset.card_le_univ Om) with hlt | heq
              · simpa using hlt
              · exact absurd (Finset.card_eq_iff_eq_univ Om |>.mp (by simpa using heq)) huniv
            have hne : Fintype.card (Fin n₁ × Fin n₂) - Om.card ≠ 0 := by omega
            rw [one_pow, one_mul, show (1:ℝ)-1 = 0 by norm_num, zero_pow hne]
          rw [hw, zero_mul]
      ·
        have hB0 : ∀ i j, B i j = 0 := by
          intro i j
          have hsum : ∀ a, ∀ b, B a b ^ 2 = 0 := by
            intro a b
            have hnn2 : ∀ a, ∀ b, (0:ℝ) ≤ B a b ^ 2 := fun a b => sq_nonneg _
            unfold frobeniusNormSq at h
            have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Finset.sum_nonneg (fun j _ => sq_nonneg (B i j)))).mp h
            have h2 := this a (Finset.mem_univ a)
            exact (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (B a j))).mp h2 b (Finset.mem_univ b)
          have := hsum i j; nlinarith [this]
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Om _ => ?_)
        have hZ0 : Z Om = 0 := by
          rw [hZ]
          unfold matrixEntrySum
          refine Finset.sum_eq_zero (fun w _ => ?_)
          show p⁻¹ * ((samplingProjection Om B) w.1 w.2 - p * B w.1 w.2) = 0
          simp [samplingProjection, hB0]
        simp only [hZ0, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
      ·
        have hsup0 : entrySupNorm B ≤ 0 := h ▸ hent
        have hB0 : ∀ i j, B i j = 0 := by
          intro i j
          have hbdd2 : ∀ a : Fin n₁, BddAbove (Set.range (fun b : Fin n₂ => |B a b|)) :=
            fun a => Set.Finite.bddAbove (Set.finite_range _)
          have hbdd1 : BddAbove (Set.range (fun a : Fin n₁ => ⨆ b : Fin n₂, |B a b|)) :=
            Set.Finite.bddAbove (Set.finite_range _)
          have hle : |B i j| ≤ entrySupNorm B := by
            unfold entrySupNorm
            exact le_trans (le_ciSup (hbdd2 i) j) (le_ciSup hbdd1 i)
          have : |B i j| ≤ 0 := le_trans hle hsup0
          have := abs_nonpos_iff.mp this; exact this
        unfold bernoulliExpectation
        refine Finset.sum_eq_zero (fun Om _ => ?_)
        have hZ0 : Z Om = 0 := by
          rw [hZ]
          unfold matrixEntrySum
          refine Finset.sum_eq_zero (fun w _ => ?_)
          show p⁻¹ * ((samplingProjection Om B) w.1 w.2 - p * B w.1 w.2) = 0
          simp [samplingProjection, hB0]
        simp only [hZ0, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
    rw [hmom0]; positivity
  ·
    push_neg at hdeg
    obtain ⟨hpne0, hpne1, hFne, hEne⟩ := hdeg
    have hppos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpne0)
    have hEpos : 0 < entryScale := lt_of_le_of_ne hentS (Ne.symm hEne)
    have hFpos : 0 < frobeniusNormSq B := lt_of_le_of_ne (by unfold frobeniusNormSq; positivity) (Ne.symm hFne)
    set V : ℝ := (1 - p) / p * frobeniusNormSq B with hVdef
    have hppos1 : p < 1 := lt_of_le_of_ne hp1 hpne1
    have h1mp0 : 0 < 1 - p := by linarith
    have hVpos : 0 < V := by rw [hVdef]; positivity

    have hFle : frobeniusNormSq B ≤ frobScale ^ 2 := by
      have hsqle : Real.sqrt (frobeniusNormSq B) ≤ frobScale := by
        have := hfrob; unfold frobeniusNorm at this; exact this
      nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ frobeniusNormSq B by unfold frobeniusNormSq; positivity),
        hsqle, hfrobS, Real.sqrt_nonneg (frobeniusNormSq B)]
    have hfrobSpos : 0 < frobScale := by
      rcases lt_or_eq_of_le hfrobS with hlt | heq
      · exact hlt
      · exfalso; rw [← heq] at hFle; simp at hFle; linarith [hFpos, hFle]

    have hVfrob : V ≤ frobScale ^ 2 / p := by
      rw [hVdef]
      have h1mp : (1 - p) ≤ 1 := by linarith
      rw [div_mul_eq_mul_div, div_le_div_iff₀ hppos hppos]
      have h1 : (1-p)*frobeniusNormSq B ≤ frobeniusNormSq B := by nlinarith [h1mp, h1mp0, hFpos.le]
      have h2 : (1-p)*frobeniusNormSq B ≤ frobScale^2 := le_trans h1 hFle
      nlinarith [h2, hppos.le]

    set lam : ℝ := min (Real.sqrt ((q:ℝ)/(2*V))) (p/entryScale) with hlam
    have hsqrtpos : 0 < Real.sqrt ((q:ℝ)/(2*V)) := Real.sqrt_pos.mpr (by positivity)
    have hlampos : 0 < lam := lt_min hsqrtpos (by positivity)
    have hlamE : lam ≤ p / entryScale := min_le_right _ _

    have hMGFpos : bernoulliExpectation p (fun Om => Real.exp (lam * Z Om))
        ≤ Real.exp (V * lam^2) := by
      have h := centered_sampling_coefficient_bernstein_mgf p hppos hp1 B entryScale lam hent hEpos hlampos.le hlamE
      have hLHS : bernoulliExpectation p (fun Om => Real.exp (lam * Z Om))
          = bernoulliExpectation p (fun Om => Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Om p B))) := by
        unfold bernoulliExpectation; apply Finset.sum_congr rfl; intro Om _; rw [hZ]
      rw [hLHS]
      refine h.trans (le_of_eq ?_)
      rw [hVdef]; ring
    have hMGFneg : bernoulliExpectation p (fun Om => Real.exp (-(lam * Z Om)))
        ≤ Real.exp (V * lam^2) := by

      have h := centered_sampling_coefficient_bernstein_mgf p hppos hp1 (-B) entryScale lam
        (by rw [entrySup_neg]; exact hent) hEpos hlampos.le hlamE
      rw [frobSq_neg] at h

      have hrw : bernoulliExpectation p (fun Om => Real.exp (-(lam * Z Om)))
          = bernoulliExpectation p (fun Om => Real.exp (lam * matrixEntrySum (centeredSamplingFluctuation Om p (-B)))) := by
        unfold bernoulliExpectation; apply Finset.sum_congr rfl; intro Om _
        simp only [hZ, coeff_neg]; congr 1; ring
      rw [hrw]
      refine h.trans (le_of_eq ?_)
      rw [hVdef]; ring

    have hmom := bernoulli_moment_from_two_sided_mgf p hp0 hp1 Z lam (Real.exp (V * lam^2)) (q:ℝ)
      hlampos hqR hMGFpos hMGFneg

    have hbridge : bernoulliExpectation p (fun Om => |Z Om| ^ q)
        = bernoulliExpectation p (fun Om => |Z Om| ^ (q:ℝ)) := by
      unfold bernoulliExpectation; apply Finset.sum_congr rfl; intro Om _
      simp only []; rw [Real.rpow_natCast]
    rw [hbridge]
    refine hmom.trans ?_

    have hbs := bound_step (q:ℝ) p V entryScale frobScale (by exact_mod_cast hq1) hppos hp1 hVpos hEpos hfrobS hVfrob

    calc 2 * ((q:ℝ) / (lam * Real.exp 1)) ^ (q:ℝ) * Real.exp (V * lam^2)
        = 2 * ((q:ℝ) / (Real.exp 1 * lam)) ^ (q:ℝ) * Real.exp (lam^2 * V) := by
          rw [mul_comm lam (Real.exp 1), mul_comm V (lam^2)]
      _ ≤ (2 * Real.sqrt 2 * (Real.sqrt ((q:ℝ)/p) * frobScale + ((q:ℝ)/p) * entryScale)) ^ (q:ℝ) := by
          rw [hlam]; exact hbs
      _ = (2 * Real.sqrt 2 * (Real.sqrt ((q:ℝ)/p) * frobScale + ((q:ℝ)/p) * entryScale)) ^ q := by
          rw [Real.rpow_natCast]
end
export P.D14 (scalar_centered_sampling_qnorm_rosenthal_estimate)

section
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 1600000

section

variable {n₁ n₂ : ℕ}

theorem P.D15.Prove75459.exp_neg_le_rpow_neg (n β : ℝ) (hn : 1 ≤ n) (q : ℝ)
    (hq : β * Real.log n ≤ q) : Real.exp (-q) ≤ Real.rpow n (-β) := by
  have hnpos : (0:ℝ) < n := lt_of_lt_of_le one_pos hn
  have hr : Real.rpow n (-β) = Real.exp (Real.log n * (-β)) := Real.rpow_def_of_pos hnpos _
  rw [hr, Real.exp_le_exp]; nlinarith [hq]

theorem P.D15.Prove75459.sqrt_ratio_le (p bl q : ℝ) (hp : 0 < p) (hbl : 0 < bl) (hq : bl ≤ q) :
    Real.sqrt (q/p) ≤ (q/bl) * Real.sqrt (bl/p) := by
  have hqpos0 : 0 < q := lt_of_lt_of_le hbl hq
  rw [show (q/bl) * Real.sqrt (bl/p) = Real.sqrt ((q/bl)^2 * (bl/p)) by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]]
  apply Real.sqrt_le_sqrt
  rw [show (q/bl)^2 * (bl/p) = q^2 / (bl * p) by field_simp]
  rw [div_le_div_iff₀ hp (by positivity)]
  have hqpos : 0 < q := lt_of_lt_of_le hbl hq
  nlinarith [hq, hbl, hp, hqpos, mul_le_mul_of_nonneg_right hq (le_of_lt hqpos)]

theorem P.D15.Prove75459.inner_ratio_le (p bl q F E : ℝ) (hp : 0 < p) (hbl : 0 < bl) (hq : bl ≤ q)
    (hF : 0 ≤ F) (hE : 0 ≤ E) :
    Real.sqrt (q/p) * F + (q/p) * E ≤ (q/bl) * (Real.sqrt (bl/p) * F + (bl/p) * E) := by
  have h1 : Real.sqrt (q/p) * F ≤ (q/bl) * (Real.sqrt (bl/p) * F) := by
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right (sqrt_ratio_le p bl q hp hbl hq) hF
  have h2 : (q/p) * E ≤ (q/bl) * ((bl/p) * E) := by
    rw [← mul_assoc]
    apply mul_le_mul_of_nonneg_right _ hE
    rw [div_mul_div_comm, div_le_div_iff₀ hp (by positivity)]
    have hqpos : 0 < q := lt_of_lt_of_le hbl hq
    nlinarith [hq, hbl, hp, hqpos]
  calc Real.sqrt (q/p) * F + (q/p) * E
      ≤ (q/bl) * (Real.sqrt (bl/p) * F) + (q/bl) * ((bl/p) * E) := add_le_add h1 h2
    _ = (q/bl) * (Real.sqrt (bl/p) * F + (bl/p) * E) := by ring

theorem P.D15.Prove75459.weight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

theorem P.D15.Prove75459.weights_sum_one (p : ℝ) :
    ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega = 1 := by
  classical
  have hpa := Fintype.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1 - p))
  simp only [add_sub_cancel, Finset.prod_const_one] at hpa
  rw [hpa]
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [bernoulliObservationWeight, Finset.prod_const, Finset.prod_const, Finset.card_compl]

theorem P.D15.Prove75459.moment_zero_of_p_zero (q : ℕ) (hq : 1 ≤ q)
    (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ) (B : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hCoeff : ∀ Omega : Finset (Fin n₁ × Fin n₂),
       Coeff Omega = matrixEntrySum (centeredSamplingFluctuation Omega (0:ℝ) B)) :
    bernoulliExpectation (0:ℝ) (fun Omega => |Coeff Omega| ^ q) = 0 := by
  have hzero : ∀ Omega : Finset (Fin n₁ × Fin n₂), Coeff Omega = 0 := by
    intro Omega; rw [hCoeff]
    unfold matrixEntrySum centeredSamplingFluctuation
    simp [inv_zero]
  unfold bernoulliExpectation
  refine Finset.sum_eq_zero (fun Omega _ => ?_)
  simp only [hzero, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]

theorem P.D15.Prove75459.moment_zero_of_n_one (q : ℕ) (hq : 1 ≤ q)
    (Coeff : Finset (Fin 1 × Fin 1) → ℝ) (B : Matrix (Fin 1) (Fin 1) ℝ)
    (hCoeff : ∀ Omega : Finset (Fin 1 × Fin 1),
       Coeff Omega = matrixEntrySum (centeredSamplingFluctuation Omega (1:ℝ) B)) :
    bernoulliExpectation (1:ℝ) (fun Omega => |Coeff Omega| ^ q) = 0 := by
  unfold bernoulliExpectation
  refine Finset.sum_eq_zero (fun Omega _ => ?_)
  simp only []
  have hsingle : ∀ x : Fin 1 × Fin 1, x = (0,0) := by
    intro x; obtain ⟨a, b⟩ := x; fin_cases a <;> fin_cases b <;> rfl
  by_cases hmem : (0,0) ∈ Omega
  · have huniv : Omega = Finset.univ :=
      Finset.eq_univ_of_forall (fun x => by rw [hsingle x]; exact hmem)
    have hC0 : Coeff Omega = 0 := by
      rw [hCoeff]
      unfold matrixEntrySum
      refine Finset.sum_eq_zero (fun w _ => ?_)
      show (1:ℝ)⁻¹ * ((samplingProjection Omega B) w.1 w.2 - (1:ℝ) * B w.1 w.2) = 0
      simp [samplingProjection, huniv]
    simp only [hC0, abs_zero, zero_pow (by omega : q ≠ 0), mul_zero]
  · have hempty : Omega = ∅ := by
      rw [← Finset.not_nonempty_iff_eq_empty]
      rintro ⟨x, hx⟩; rw [hsingle x] at hx; exact hmem hx
    have hw : bernoulliObservationWeight (1:ℝ) Omega = 0 := by
      rw [hempty]; unfold bernoulliObservationWeight; simp
    rw [hw, zero_mul]

end

open P.D15.Prove75459 in

theorem P.D15.scalar_centered_sampling_qmoment_bernstein_estimate :
    ∃ Cbern cbern : ℝ, 0 < Cbern ∧ 0 < cbern ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
        (B : Matrix (Fin n₁) (Fin n₂) ℝ)
        (entryScale frobScale : ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤ entryScale →
        frobeniusNorm B ≤ frobScale →
        ∃ q : ℕ, 1 ≤ q ∧
          bernoulliExpectation ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
              (fun Omega => |Coeff Omega| ^ q) ≤
            (Cbern *
                (Real.sqrt
                    ((β * Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  frobScale +
                  ((β * Real.log (↑(max n₁ n₂))) /
                    ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                  entryScale)) ^ q *
              (cbern * Real.rpow (↑(max n₁ n₂)) (-β)) := by
  obtain ⟨C, hCpos, hcore⟩ := scalar_centered_sampling_qnorm_rosenthal_estimate
  refine ⟨2 * Real.exp 1 * C, 1, by positivity, one_pos, ?_⟩
  intro β hβ n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hentry hfrob
  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set nn : ℝ := (↑(max n₁ n₂) : ℝ) with hnn
  set bl : ℝ := β * Real.log nn with hbl
  have hn1n2 : (0:ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hp0 : 0 ≤ p := by rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp, div_le_one hn1n2]
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hmle
    push_cast at this; linarith
  have hmaxpos : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _)
  have hnn1 : 1 ≤ nn := by rw [hnn]; exact_mod_cast hmaxpos
  have hnnpos : 0 < nn := lt_of_lt_of_le one_pos hnn1
  have hentrySN_nn : 0 ≤ entrySupNorm B :=
    Real.iSup_nonneg (fun i => Real.iSup_nonneg (fun j => abs_nonneg _))
  have hfrobN_nn : 0 ≤ frobeniusNorm B := by unfold frobeniusNorm; exact Real.sqrt_nonneg _
  have hE_nn : 0 ≤ entryScale := le_trans hentrySN_nn hentry
  have hF_nn : 0 ≤ frobScale := le_trans hfrobN_nn hfrob

  have hrpow_nn : 0 ≤ Real.rpow nn (-β) := le_of_lt (Real.rpow_pos_of_pos hnnpos _)

  by_cases hpz : p = 0
  · refine ⟨1, le_refl 1, ?_⟩
    have hcoeff0 : ∀ Omega : Finset (Fin n₁ × Fin n₂),
        Coeff Omega = matrixEntrySum (centeredSamplingFluctuation Omega (0:ℝ) B) := by
      intro Omega; rw [hCoeff, hpz]
    have hmom0 := moment_zero_of_p_zero (n₁ := n₁) (n₂ := n₂) 1 (le_refl 1) Coeff B hcoeff0
    rw [hpz, hmom0]

    simp only [div_zero, Real.sqrt_zero, zero_mul, add_zero, mul_zero, pow_one, le_refl]
  ·
    have hppos : 0 < p := lt_of_le_of_ne hp0 (Ne.symm hpz)
    by_cases hmax1 : max n₁ n₂ = 1
    ·
      have hn1e : n₁ = 1 := by omega
      have hn2e : n₂ = 1 := by omega
      subst hn1e; subst hn2e

      have hpm : p = (m : ℝ) := by rw [hp]; norm_num
      have hmpos : 0 < m := by
        by_contra h; push_neg at h; interval_cases m; simp [hpm] at hppos
      have hm1 : m = 1 := by omega
      have hpeq1 : p = 1 := by rw [hpm, hm1]; norm_num
      refine ⟨1, le_refl 1, ?_⟩
      have hcoeff1 : ∀ Omega : Finset (Fin 1 × Fin 1),
          Coeff Omega = matrixEntrySum (centeredSamplingFluctuation Omega (1:ℝ) B) := by
        intro Omega; rw [hCoeff, hpeq1]
      have hmom0 := moment_zero_of_n_one 1 (le_refl 1) Coeff B hcoeff1
      have hbl0 : bl = 0 := by
        rw [hbl, hnn]; norm_num
      rw [hpeq1, hmom0, hbl0]
      simp only [zero_div, Real.sqrt_zero, zero_mul, add_zero, mul_zero, pow_one, le_refl]
    ·
      have hmax2 : 2 ≤ max n₁ n₂ := by omega
      have hnn2 : 2 ≤ nn := by rw [hnn]; exact_mod_cast hmax2
      have hlog2 : Real.log 2 ≤ Real.log nn := Real.log_le_log (by norm_num) hnn2
      have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
      have hblpos : 0 < bl := by
        rw [hbl]; exact mul_pos (by linarith) (lt_of_lt_of_le hlog2pos hlog2)
      have hbl1 : 1 < bl := by
        rw [hbl]
        have hstep : (2:ℝ) * Real.log 2 ≤ β * Real.log nn := by
          apply le_trans (le_of_lt (mul_lt_mul_of_pos_right hβ hlog2pos))
          exact mul_le_mul_of_nonneg_left hlog2 (by linarith)
        nlinarith [Real.log_two_gt_d9, hstep, hlog2pos]

      set q : ℕ := ⌈bl⌉₊ with hqdef
      have hqge : bl ≤ (q : ℝ) := Nat.le_ceil bl
      have hqle : (q : ℝ) ≤ bl + 1 := by
        rw [hqdef]; exact le_of_lt (Nat.ceil_lt_add_one (le_of_lt hblpos))
      have hq1 : 1 ≤ q := by
        rw [hqdef]; exact Nat.one_le_ceil_iff.mpr hblpos
      have hq2bl : (q : ℝ) ≤ 2 * bl := by nlinarith [hqge, hqle, hbl1]
      have hqpos : (0:ℝ) < q := by exact_mod_cast hq1
      refine ⟨q, hq1, ?_⟩

      have hc := hcore n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hentry hfrob q hq1
      rw [← hp] at hc

      set M : ℝ := Real.sqrt (bl/p) * frobScale + (bl/p) * entryScale with hM
      set J : ℝ := Real.sqrt ((q:ℝ)/p) * frobScale + ((q:ℝ)/p) * entryScale with hJ

      have hJM : J ≤ (q/bl) * M := by
        rw [hJ, hM]; exact inner_ratio_le p bl q frobScale entryScale hppos hblpos hqge hF_nn hE_nn
      have hMnn : 0 ≤ M := by
        rw [hM]; apply add_nonneg
        · exact mul_nonneg (Real.sqrt_nonneg _) hF_nn
        · exact mul_nonneg (by positivity) hE_nn
      have hqblle2 : (q:ℝ)/bl ≤ 2 := by rw [div_le_iff₀ hblpos]; linarith [hq2bl]
      have hJ2M : J ≤ 2 * M := by
        refine le_trans hJM ?_
        have := mul_le_mul_of_nonneg_right hqblle2 hMnn
        linarith [this]
      have hJnn : 0 ≤ J := by
        rw [hJ]; apply add_nonneg
        · exact mul_nonneg (Real.sqrt_nonneg _) hF_nn
        · exact mul_nonneg (by positivity) hE_nn

      have hstep2 : (C * J)^q ≤ (2 * C * M)^q := by
        apply pow_le_pow_left₀ (by positivity)
        calc C * J ≤ C * (2 * M) := by
              exact mul_le_mul_of_nonneg_left hJ2M (le_of_lt hCpos)
          _ = 2 * C * M := by ring

      have hexp : Real.exp (-(q:ℝ)) ≤ Real.rpow nn (-β) :=
        exp_neg_le_rpow_neg nn β hnn1 q (le_trans hqge (le_refl _))
      have hexpq_pos : 0 < Real.exp 1 ^ q := by positivity
      have h2CM_nn : 0 ≤ (2 * C * M)^q := by positivity
      have hfac : 1 ≤ (Real.exp 1)^q * Real.rpow nn (-β) := by
        have hee : (Real.exp 1)^q = Real.exp (q:ℝ) := by
          rw [← Real.exp_nat_mul]; ring_nf
        rw [hee]
        calc (1:ℝ) = Real.exp (q:ℝ) * Real.exp (-(q:ℝ)) := by
              rw [← Real.exp_add]; simp
          _ ≤ Real.exp (q:ℝ) * Real.rpow nn (-β) :=
              mul_le_mul_of_nonneg_left hexp (le_of_lt (Real.exp_pos _))
      have hstep3 : (2 * C * M)^q ≤ (2 * Real.exp 1 * C * M)^q * (1 * Real.rpow nn (-β)) := by
        have hbase : (2 * Real.exp 1 * C * M)^q = (2 * C * M)^q * (Real.exp 1)^q := by
          rw [← mul_pow]; congr 1; ring
        have hrw : (2 * Real.exp 1 * C * M)^q * (1 * Real.rpow nn (-β))
            = (2 * C * M)^q * ((Real.exp 1)^q * Real.rpow nn (-β)) := by
          rw [hbase, one_mul, mul_assoc]
        rw [hrw]
        exact le_mul_of_one_le_right h2CM_nn hfac

      calc bernoulliExpectation p (fun Omega => |Coeff Omega| ^ q)
          ≤ (C * J)^q := hc
        _ ≤ (2 * C * M)^q := hstep2
        _ ≤ (2 * Real.exp 1 * C * M)^q * (1 * Real.rpow nn (-β)) := hstep3
end
export P.D15 (scalar_centered_sampling_qmoment_bernstein_estimate)

section
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

section

variable {n₁ n₂ : ℕ}

theorem P.D16.ProveMarkov.weights_sum_one (p : ℝ) :
    ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega = 1 := by
  classical
  have hpa := Fintype.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1 - p))
  simp only [add_sub_cancel, Finset.prod_const_one] at hpa
  rw [hpa]
  apply Finset.sum_congr rfl
  intro t _
  rw [bernoulliObservationWeight, Finset.prod_const, Finset.prod_const,
    Finset.card_compl]

theorem P.D16.ProveMarkov.weight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

theorem P.D16.ProveMarkov.prob_add_compl (p : ℝ) (Event : Finset (Fin n₁ × Fin n₂) → Prop) :
    bernoulliEventProb p Event +
      bernoulliEventProb p (fun Omega => ¬ Event Omega) = 1 := by
  classical
  unfold bernoulliEventProb
  rw [← Finset.sum_add_distrib, ← weights_sum_one (n₁ := n₁) (n₂ := n₂) p]
  apply Finset.sum_congr rfl
  intro Omega _
  by_cases h : Event Omega <;> simp [h]

end

open P.D16.ProveMarkov in

theorem P.D16.scalar_centered_sampling_markov_tail_from_qmoment_bound
    {n₁ n₂ : ℕ} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (q : ℕ) (hq : 1 ≤ q)
    (t failProb : ℝ) (ht : 0 < t) (hfail : 0 ≤ failProb)
    (hmoment : bernoulliExpectation p (fun Omega => |Z Omega| ^ q) ≤ t ^ q * failProb) :
    bernoulliEventProb p (fun Omega => |Z Omega| ≤ t) ≥ 1 - failProb := by
  classical
  set Bad : Finset (Fin n₁ × Fin n₂) → Prop := fun Omega => ¬ (|Z Omega| ≤ t) with hBad
  have htq : (0:ℝ) < t ^ q := by positivity
  have hkey : t ^ q * bernoulliEventProb p Bad ≤
      bernoulliExpectation p (fun Omega => |Z Omega| ^ q) := by
    unfold bernoulliEventProb bernoulliExpectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro Omega _
    by_cases h : Bad Omega
    · simp only [h, if_true]
      have hlt : t < |Z Omega| := by rw [hBad] at h; push_neg at h; exact h
      have hpow : t ^ q ≤ |Z Omega| ^ q :=
        pow_le_pow_left₀ (le_of_lt ht) (le_of_lt hlt) q
      have hw : 0 ≤ bernoulliObservationWeight p Omega := weight_nonneg p hp0 hp1 Omega
      calc t ^ q * bernoulliObservationWeight p Omega
          = bernoulliObservationWeight p Omega * t ^ q := by ring
        _ ≤ bernoulliObservationWeight p Omega * |Z Omega| ^ q :=
              mul_le_mul_of_nonneg_left hpow hw
    · simp only [h, if_false, mul_zero]
      have hw : 0 ≤ bernoulliObservationWeight p Omega := weight_nonneg p hp0 hp1 Omega
      positivity
  have hPbad : bernoulliEventProb p Bad ≤ failProb := by
    have h1 : t ^ q * bernoulliEventProb p Bad ≤ t ^ q * failProb :=
      le_trans hkey hmoment
    exact le_of_mul_le_mul_left h1 htq
  have hsplit : bernoulliEventProb p (fun Omega => |Z Omega| ≤ t) +
      bernoulliEventProb p Bad = 1 := by
    have := prob_add_compl (n₁ := n₁) (n₂ := n₂) p (fun Omega => |Z Omega| ≤ t)
    rw [hBad]; exact this
  linarith [hPbad, hsplit]
end
export P.D16 (scalar_centered_sampling_markov_tail_from_qmoment_bound)

section
open MatrixCompletion
open scoped BigOperators Classical

set_option maxHeartbeats 800000

section

variable {n₁ n₂ : ℕ}

theorem P.D17.Prove3cbb.weight_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Omega : Finset (Fin n₁ × Fin n₂)) : 0 ≤ bernoulliObservationWeight p Omega := by
  unfold bernoulliObservationWeight
  have : 0 ≤ 1 - p := by linarith
  positivity

theorem P.D17.Prove3cbb.weights_sum_one (p : ℝ) :
    ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega = 1 := by
  classical
  have hpa := Fintype.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1 - p))
  simp only [add_sub_cancel, Finset.prod_const_one] at hpa
  rw [hpa]
  apply Finset.sum_congr rfl
  intro t _
  rw [bernoulliObservationWeight, Finset.prod_const, Finset.prod_const,
    Finset.card_compl]

theorem P.D17.Prove3cbb.tail_at_zero (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Z : Finset (Fin n₁ × Fin n₂) → ℝ) (q : ℕ) (hq : 1 ≤ q)
    (failProb : ℝ) (hfail : 0 ≤ failProb)
    (hmom0 : bernoulliExpectation p (fun Omega => |Z Omega| ^ q) ≤ 0) :
    bernoulliEventProb p (fun Omega => |Z Omega| ≤ 0) ≥ 1 - failProb := by
  classical

  have hterm_nn : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      0 ≤ bernoulliObservationWeight p Omega * |Z Omega| ^ q := by
    intro Omega
    have := weight_nonneg (n₁ := n₁) (n₂ := n₂) p hp0 hp1 Omega
    positivity
  have hsum0 : ∑ Omega : Finset (Fin n₁ × Fin n₂),
      bernoulliObservationWeight p Omega * |Z Omega| ^ q = 0 := by
    have hge : (0:ℝ) ≤ ∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega * |Z Omega| ^ q :=
      Finset.sum_nonneg (fun Omega _ => hterm_nn Omega)
    have hle : (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega * |Z Omega| ^ q) ≤ 0 := by
      unfold bernoulliExpectation at hmom0; exact hmom0
    linarith
  have heach : ∀ Omega : Finset (Fin n₁ × Fin n₂),
      bernoulliObservationWeight p Omega * |Z Omega| ^ q = 0 := by
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun Omega _ => hterm_nn Omega)).1 hsum0
    intro Omega; exact h Omega (Finset.mem_univ _)

  have hbe : bernoulliEventProb p (fun Omega => |Z Omega| ≤ 0)
      = ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega := by
    unfold bernoulliEventProb
    apply Finset.sum_congr rfl
    intro Omega _
    by_cases h : |Z Omega| ≤ 0
    · simp [h]
    ·
      push_neg at h
      have hZpos : 0 < |Z Omega| := h
      have hpowpos : 0 < |Z Omega| ^ q := by positivity
      have hw0 : bernoulliObservationWeight p Omega = 0 := by
        have := heach Omega
        rcases mul_eq_zero.1 this with h1 | h2
        · exact h1
        · exact absurd h2 (ne_of_gt hpowpos)
      simp [h, hw0]
  rw [hbe, weights_sum_one]
  linarith

end

open P.D17.Prove3cbb in

theorem P.D17.scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales :
    ∃ Cbern cbern : ℝ, 0 < Cbern ∧ 0 < cbern ∧
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ m : ℕ), 0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
      ∀ (Coeff : Finset (Fin n₁ × Fin n₂) → ℝ)
        (B : Matrix (Fin n₁) (Fin n₂) ℝ)
        (entryScale frobScale : ℝ),
        (∀ Omega : Finset (Fin n₁ × Fin n₂),
          Coeff Omega =
            matrixEntrySum
              (centeredSamplingFluctuation Omega
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) B)) →
        entrySupNorm B ≤ entryScale →
        frobeniusNorm B ≤ frobScale →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              |Coeff Omega| ≤
                Cbern *
                  (Real.sqrt
                      ((β * Real.log (↑(max n₁ n₂))) /
                        ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    frobScale +
                    ((β * Real.log (↑(max n₁ n₂))) /
                      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
                    entryScale)) ≥
          1 - cbern * Real.rpow (↑(max n₁ n₂)) (-β) := by
  obtain ⟨Cbern, cbern, hCbern, hcbern, hcore⟩ :=
    scalar_centered_sampling_qmoment_bernstein_estimate
  refine ⟨Cbern, cbern, hCbern, hcbern, ?_⟩
  intro β hβ n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hentry hfrob

  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  set n : ℝ := (↑(max n₁ n₂) : ℝ) with hn
  set T : ℝ := Cbern *
      (Real.sqrt ((β * Real.log n) / p) * frobScale +
        ((β * Real.log n) / p) * entryScale) with hT
  set failProb : ℝ := cbern * Real.rpow n (-β) with hfp

  have hn1n2 : (0:ℝ) < (n₁ : ℝ) * (n₂ : ℝ) := by positivity
  have hp0 : 0 ≤ p := by
    rw [hp]; positivity
  have hp1 : p ≤ 1 := by
    rw [hp]
    rw [div_le_one hn1n2]
    have : (m : ℝ) ≤ ((n₁ * n₂ : ℕ) : ℝ) := by exact_mod_cast hmle
    push_cast at this; linarith

  have hnpos : (0:ℝ) < n := by
    rw [hn]; have : 0 < max n₁ n₂ := lt_of_lt_of_le hn1 (le_max_left _ _); exact_mod_cast this
  have hfail : 0 ≤ failProb := by
    rw [hfp]; apply mul_nonneg (le_of_lt hcbern); exact le_of_lt (Real.rpow_pos_of_pos hnpos _)

  obtain ⟨q, hq, hmoment⟩ := hcore β hβ n₁ n₂ m hn1 hn2 hmle Coeff B entryScale frobScale hCoeff hentry hfrob

  rw [← hp, ← hn, ← hT, ← hfp] at hmoment

  have hlogn_nn : 0 ≤ Real.log n := by
    rw [hn]
    apply Real.log_nonneg
    have : 1 ≤ max n₁ n₂ := le_trans hn1 (le_max_left _ _)
    exact_mod_cast this
  have hbeta_log_nn : 0 ≤ β * Real.log n := mul_nonneg (by linarith) hlogn_nn
  have hbl_div_nn : 0 ≤ (β * Real.log n) / p := div_nonneg hbeta_log_nn hp0

  have hentrySN_nn : 0 ≤ entrySupNorm B := by
    unfold entrySupNorm
    apply Real.iSup_nonneg
    intro i
    apply Real.iSup_nonneg
    intro j
    exact abs_nonneg _
  have hfrobN_nn : 0 ≤ frobeniusNorm B := by
    unfold frobeniusNorm; exact Real.sqrt_nonneg _
  have hentry_nn : 0 ≤ entryScale := le_trans hentrySN_nn hentry
  have hfrob_nn : 0 ≤ frobScale := le_trans hfrobN_nn hfrob
  have hbracket_nn : 0 ≤ Real.sqrt ((β * Real.log n) / p) * frobScale +
      ((β * Real.log n) / p) * entryScale := by
    apply add_nonneg
    · exact mul_nonneg (Real.sqrt_nonneg _) hfrob_nn
    · exact mul_nonneg hbl_div_nn hentry_nn
  have hT_nn : 0 ≤ T := by rw [hT]; exact mul_nonneg (le_of_lt hCbern) hbracket_nn

  rcases eq_or_lt_of_le hT_nn with hT0 | hTpos
  ·
    have hTeq : T = 0 := hT0.symm
    have hTq0 : T ^ q = 0 := by rw [hTeq]; exact zero_pow (by omega)
    have hmom0 : bernoulliExpectation p (fun Omega => |Coeff Omega| ^ q) ≤ 0 := by
      rw [hTq0, zero_mul] at hmoment; exact hmoment

    have hres := tail_at_zero (n₁ := n₁) (n₂ := n₂) p hp0 hp1 Coeff q hq failProb hfail hmom0
    rw [hTeq]; exact hres
  ·
    exact scalar_centered_sampling_markov_tail_from_qmoment_bound p hp0 hp1 Coeff q hq
      T failProb hTpos hfail hmoment
end
export P.D17 (scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales)

section
open MatrixCompletion
open scoped Classical BigOperators

theorem P.D18.bernoulli_event_probability_mono
    {n₁ n₂ : ℕ} (p : ℝ)
    (EventA EventB : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    (∀ Omega, EventA Omega → EventB Omega) →
    bernoulliEventProb p EventA ≤ bernoulliEventProb p EventB := by
  intro hp0 hp1 hAB
  have hw : ∀ Om : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Om := by
    intro Om
    unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  unfold bernoulliEventProb
  apply Finset.sum_le_sum
  intro Omega _
  by_cases hA : EventA Omega
  · rw [if_pos hA, if_pos (hAB Omega hA)]
  · rw [if_neg hA]
    by_cases hB : EventB Omega
    · rw [if_pos hB]; exact hw Omega
    · rw [if_neg hB]
end
export P.D18 (bernoulli_event_probability_mono)

section
open MatrixCompletion
open scoped Classical BigOperators

set_option maxHeartbeats 2000000

section

theorem P.D19.Bot5_minpoint.beta_log_ge_one (β : ℝ) (hβ : 2 < β) (x : ℝ) (hx : 2 ≤ x) :
    1 ≤ β * Real.log x := by
  have hlog2 : Real.log 2 ≤ Real.log x := Real.log_le_log (by norm_num) hx
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h4 : (1:ℝ) ≤ 2 * Real.log 2 := by
    rw [show (2:ℝ) * Real.log 2 = Real.log 4 by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring]
    rw [show (1:ℝ) = Real.log (Real.exp 1) by rw [Real.log_exp]]
    apply Real.log_le_log (Real.exp_pos 1)
    have := Real.exp_one_lt_three
    linarith
  calc (1:ℝ) ≤ 2 * Real.log 2 := h4
    _ ≤ β * Real.log x := by
        apply mul_le_mul (le_of_lt hβ) hlog2 (le_of_lt hlog2pos) (by linarith)

theorem P.D19.Bot5_minpoint.min_mul_max_real (n₁ n₂ : ℕ) :
    (↑(min n₁ n₂) : ℝ) * (↑(max n₁ n₂) : ℝ) = (n₁ : ℝ) * (n₂ : ℝ) := by
  rw [← Nat.cast_mul]; exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (min_mul_max n₁ n₂)

theorem P.D19.Bot5_minpoint.rpow_three_half (x : ℝ) (hx : 0 ≤ x) :
    Real.rpow x ((3:ℝ)/2) = x * Real.sqrt x := by
  have h1 : Real.rpow x ((3:ℝ)/2) = Real.sqrt (x ^ 3) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 3, ← Real.rpow_mul hx]
    norm_num
  rw [h1, show x ^ 3 = x ^ 2 * x by ring, Real.sqrt_mul (by positivity),
      Real.sqrt_sq hx]

theorem P.D19.Bot5_minpoint.bernoulliEventProb_nonneg {n1 n2 : Nat} (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Event : Finset (Fin n1 × Fin n2) → Prop) :
    0 ≤ bernoulliEventProb p Event := by
  unfold bernoulliEventProb
  apply Finset.sum_nonneg
  intro Omega _
  by_cases h : Event Omega
  · rw [if_pos h]; unfold bernoulliObservationWeight
    apply mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  · rw [if_neg h]

end

open P.D19.Bot5_minpoint

end
export P.D19.Bot5_minpoint (bernoulliEventProb_nonneg)

section
open MatrixCompletion

open MatrixCompletion

theorem P.D20.sample_ratio_between_zero_and_one
    (n₁ n₂ m : ℕ) :
    0 < n₁ → 0 < n₂ → m ≤ n₁ * n₂ →
    0 ≤ ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ∧
      ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) ≤ 1 := by
  intro hn₁ hn₂ hm
  constructor
  · exact div_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  · have hden_pos : 0 < (n₁ : ℝ) * (n₂ : ℝ) := by
      exact mul_pos (Nat.cast_pos.mpr hn₁) (Nat.cast_pos.mpr hn₂)
    have hnum_le_den : (m : ℝ) ≤ (n₁ : ℝ) * (n₂ : ℝ) := by
      exact_mod_cast hm
    rw [div_le_iff₀ hden_pos]
    simpa using hnum_le_den
end
export P.D20 (sample_ratio_between_zero_and_one)

section
open MatrixCompletion
open scoped Classical BigOperators
open Finset

private theorem P.D21.bern_total {n₁ n₂ : ℕ} (p : ℝ) :
    ∑ Omega : Finset (Fin n₁ × Fin n₂), bernoulliObservationWeight p Omega = 1 := by
  unfold bernoulliObservationWeight
  rw [← Finset.powerset_univ]
  have key := Finset.prod_add (fun _ : Fin n₁ × Fin n₂ => p) (fun _ => (1:ℝ) - p) Finset.univ
  have hL : ∏ _i : Fin n₁ × Fin n₂, (p + (1 - p)) = 1 := by
    rw [Finset.prod_const, Finset.card_univ]
    have h1 : p + (1 - p) = 1 := by ring
    rw [h1, one_pow]
  rw [hL] at key
  refine Eq.trans ?_ key.symm
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.prod_const, Finset.prod_const]
  rw [show (univ \ t).card = Fintype.card (Fin n₁ × Fin n₂) - t.card from by
        rw [← Finset.compl_eq_univ_sdiff, Finset.card_compl]]

theorem P.D21.bernoulli_event_intersection_probability_from_lower_bounds
    {n₁ n₂ : ℕ} (p cA cB failureScale : ℝ)
    (EventA EventB : Finset (Fin n₁ × Fin n₂) → Prop) :
    0 ≤ p → p ≤ 1 →
    bernoulliEventProb p EventA ≥ 1 - cA * failureScale →
    bernoulliEventProb p EventB ≥ 1 - cB * failureScale →
    bernoulliEventProb p (fun Omega => EventA Omega ∧ EventB Omega) ≥
      1 - (cA + cB) * failureScale := by
  intro hp0 hp1 hA hB
  have hw : ∀ Om : Finset (Fin n₁ × Fin n₂), 0 ≤ bernoulliObservationWeight p Om := by
    intro Om
    unfold bernoulliObservationWeight
    exact mul_nonneg (pow_nonneg hp0 _) (pow_nonneg (by linarith) _)
  have key : bernoulliEventProb p EventA + bernoulliEventProb p EventB
              - bernoulliEventProb p (fun Omega => EventA Omega ∧ EventB Omega) ≤ 1 := by
    rw [← bern_total (n₁ := n₁) (n₂ := n₂) p]
    unfold bernoulliEventProb
    rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro Omega _
    have hwO := hw Omega
    by_cases hA' : EventA Omega
    · by_cases hB' : EventB Omega
      · simp only [if_pos hA', if_pos hB', if_pos (And.intro hA' hB')]; linarith
      · have hn : ¬ (EventA Omega ∧ EventB Omega) := fun h => hB' h.2
        simp only [if_pos hA', if_neg hB', if_neg hn]; linarith
    · have hn : ¬ (EventA Omega ∧ EventB Omega) := fun h => hA' h.1
      by_cases hB' : EventB Omega
      · simp only [if_neg hA', if_pos hB', if_neg hn]; linarith
      · simp only [if_neg hA', if_neg hB', if_neg hn]; linarith
  have hexp : (cA + cB) * failureScale = cA * failureScale + cB * failureScale := by ring
  linarith [key, hA, hB, hexp]
end
export P.D21 (bernoulli_event_intersection_probability_from_lower_bounds)

section
open MatrixCompletion

open scoped Classical BigOperators

private lemma P.D22.bernoulliObservationWeight_sum_eq_one
    {n₁ n₂ : ℕ} {p : ℝ} :
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega) = 1 := by
  classical
  let α := Fin n₁ × Fin n₂
  let N := Fintype.card α
  have hsum_powerset :
      (∑ Omega : Finset α,
          p ^ Omega.card * (1 - p) ^ (N - Omega.card)) =
        ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := by
    rw [← Finset.powerset_univ]
    rw [Finset.sum_powerset]
    apply Finset.sum_congr rfl
    intro k hk
    have hcard :
        (Finset.univ : Finset α).card = N := by
      simp [N]
    have h :=
      Finset.sum_powersetCard k (Finset.univ : Finset α)
        (fun j : ℕ => p ^ j * (1 - p) ^ (N - j))
    simpa [hcard, mul_assoc, mul_left_comm, mul_comm] using h
  calc
    (∑ Omega : Finset (Fin n₁ × Fin n₂),
        bernoulliObservationWeight p Omega)
        = ∑ Omega : Finset α,
            p ^ Omega.card * (1 - p) ^ (N - Omega.card) := by
          simp [α, N, bernoulliObservationWeight]
    _ = ∑ k ∈ Finset.range (N + 1),
          (Nat.choose N k : ℝ) * (p ^ k * (1 - p) ^ (N - k)) := hsum_powerset
    _ = ∑ k ∈ Finset.range (N + 1),
          p ^ k * (1 - p) ^ (N - k) * (Nat.choose N k : ℝ) := by
          apply Finset.sum_congr rfl
          intro k hk
          ring
    _ = (p + (1 - p)) ^ N := by
          rw [add_pow]
    _ = 1 := by
          ring

private lemma P.D22.bernoulliEventProb_true
    {n₁ n₂ : ℕ} (p : ℝ) :
    bernoulliEventProb p (fun _ : Finset (Fin n₁ × Fin n₂) => True) = 1 := by
  unfold bernoulliEventProb
  simpa using (bernoulliObservationWeight_sum_eq_one (n₁ := n₁) (n₂ := n₂) (p := p))

private theorem P.D22.finite_pair_intersection_aux
    {n₁ n₂ : ℕ} (p c failureScale : ℝ)
    (Event :
      ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) →
        Finset (Fin n₁ × Fin n₂) → Prop)
    (hp : 0 ≤ p) (hp_one : p ≤ 1)
    (hPoint :
      ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
        bernoulliEventProb p (Event pair) ≥ 1 - c * failureScale) :
    ∀ s : Finset ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)),
      bernoulliEventProb p
          (fun Omega =>
            ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
              pair ∈ s → Event pair Omega) ≥
        1 - (((s.card : ℝ) * c) * failureScale) := by
  intro s
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [bernoulliEventProb_true]
  | insert a s ha ih =>
      have hA :
          bernoulliEventProb p (Event a) ≥ 1 - c * failureScale :=
        hPoint a
      have hB :
          bernoulliEventProb p
              (fun Omega =>
                ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
                  pair ∈ s → Event pair Omega) ≥
            1 - ((s.card : ℝ) * c) * failureScale :=
        ih
      have hInter :=
        bernoulli_event_intersection_probability_from_lower_bounds
          p c ((s.card : ℝ) * c) failureScale
          (Event a)
          (fun Omega =>
            ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
              pair ∈ s → Event pair Omega)
          hp hp_one hA hB
      have hcard : (insert a s).card = s.card + 1 := by
        simp [ha]
      have hconst :
          (c + (s.card : ℝ) * c) * failureScale =
            (((insert a s).card : ℝ) * c) * failureScale := by
        rw [hcard, Nat.cast_add, Nat.cast_one]
        ring
      have hevent :
          (fun Omega : Finset (Fin n₁ × Fin n₂) =>
              Event a Omega ∧
                (∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
                  pair ∈ s → Event pair Omega)) =
            (fun Omega =>
              ∀ pair : (Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂),
                pair ∈ insert a s → Event pair Omega) := by
        funext Omega
        apply propext
        constructor
        · intro h pair hpair
          rcases h with ⟨haEvent, hsEvent⟩
          by_cases hpa : pair = a
          · simpa [hpa] using haEvent
          · exact hsEvent pair (by simpa [Finset.mem_insert, hpa] using hpair)
        · intro h
          constructor
          · exact h a (by simp)
          · intro pair hpair
            exact h pair (by simp [hpair])
      simpa [hevent, hconst] using hInter

theorem P.D22.bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
    (Cpoint cpoint : ℝ) :
    0 < Cpoint → 0 < cpoint →
    ∀ (p scale failureScale : ℝ), 0 ≤ p → p ≤ 1 →
      ∀ (n₁ n₂ : ℕ),
        ∀ Coeff : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) →
          Finset (Fin n₁ × Fin n₂) → ℝ,
        (∀ w1 w2 : Fin n₁ × Fin n₂,
          bernoulliEventProb p
              (fun Omega => |Coeff w1 w2 Omega| ≤ Cpoint * scale) ≥
            1 - cpoint * failureScale) →
        bernoulliEventProb p
            (fun Omega =>
              ∀ w1 w2 : Fin n₁ × Fin n₂,
                |Coeff w1 w2 Omega| ≤ Cpoint * scale) ≥
          1 -
            (((Fintype.card
              ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) *
              cpoint) * failureScale) := by
  intro _hCpoint _hcpoint p scale failureScale hp hp_one n₁ n₂ Coeff hPoint
  have h :=
    finite_pair_intersection_aux p cpoint failureScale
      (fun pair Omega => |Coeff pair.1 pair.2 Omega| ≤ Cpoint * scale)
      hp hp_one
      (by
        intro pair
        exact hPoint pair.1 pair.2)
      (Finset.univ :
        Finset ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)))
  simpa [Prod.forall] using h
end
export P.D22 (bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor)

section
open MatrixCompletion

theorem P.D23.pair_coordinate_cardinality_loss_absorbed_by_beta_shift
    (β c : ℝ) (n₁ n₂ : ℕ) :
    2 < β → 0 < c → 0 < n₁ → 0 < n₂ →
    (((Fintype.card
        ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) * c) *
        Real.rpow (↑(max n₁ n₂)) (-(β + 4))) ≤
      c * Real.rpow (↑(max n₁ n₂)) (-β) := by
  intro _hβ hc hn₁ hn₂
  let N : ℕ := max n₁ n₂
  have hN_pos_nat : 0 < N := lt_of_lt_of_le hn₁ (Nat.le_max_left n₁ n₂)
  have hN_pos : 0 < (N : ℝ) := by exact_mod_cast hN_pos_nat
  have hc_nonneg : 0 ≤ c := le_of_lt hc
  have hfail_nonneg : 0 ≤ Real.rpow (N : ℝ) (-(β + 4)) :=
    Real.rpow_nonneg (le_of_lt hN_pos) _
  have hcard_nat :
      Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) ≤ N ^ 4 := by
    have hn₁_le : n₁ ≤ N := Nat.le_max_left n₁ n₂
    have hn₂_le : n₂ ≤ N := Nat.le_max_right n₁ n₂
    have hprod : n₁ * n₂ ≤ N * N := Nat.mul_le_mul hn₁_le hn₂_le
    have hprod2 : (n₁ * n₂) * (n₁ * n₂) ≤ (N * N) * (N * N) :=
      Nat.mul_le_mul hprod hprod
    calc
      Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂))
          = (n₁ * n₂) * (n₁ * n₂) := by
              simp [Fintype.card_prod]
      _ ≤ (N * N) * (N * N) := hprod2
      _ = N ^ 4 := by ring
  have hcard_real :
      (Fintype.card ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) ≤
        (N : ℝ) ^ 4 := by
    exact_mod_cast hcard_nat
  have hmul :
      ((Fintype.card
          ((Fin n₁ × Fin n₂) × (Fin n₁ × Fin n₂)) : ℝ) * c) *
          Real.rpow (N : ℝ) (-(β + 4)) ≤
        (((N : ℝ) ^ 4 * c) * Real.rpow (N : ℝ) (-(β + 4))) := by
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcard_real hc_nonneg) hfail_nonneg
  have hrpow :
      ((N : ℝ) ^ 4) * Real.rpow (N : ℝ) (-(β + 4)) =
        Real.rpow (N : ℝ) (-β) := by
    calc
      ((N : ℝ) ^ 4) * Real.rpow (N : ℝ) (-(β + 4))
          = Real.rpow (N : ℝ) (4 : ℝ) *
              Real.rpow (N : ℝ) (-(β + 4)) := by
                exact congrArg
                  (fun t => t * Real.rpow (N : ℝ) (-(β + 4)))
                  (Real.rpow_natCast (N : ℝ) 4).symm
      _ = Real.rpow (N : ℝ) ((4 : ℝ) + (-(β + 4))) := by
                exact (Real.rpow_add hN_pos (4 : ℝ) (-(β + 4))).symm
      _ = Real.rpow (N : ℝ) (-β) := by
                congr 1
                ring
  have htarget :
      (((N : ℝ) ^ 4 * c) * Real.rpow (N : ℝ) (-(β + 4))) =
        c * Real.rpow (N : ℝ) (-β) := by
    calc
      (((N : ℝ) ^ 4 * c) * Real.rpow (N : ℝ) (-(β + 4)))
          = c * (((N : ℝ) ^ 4) * Real.rpow (N : ℝ) (-(β + 4))) := by
              ring
      _ = c * Real.rpow (N : ℝ) (-β) := by
              rw [hrpow]
  simpa [N] using le_trans hmul (le_of_eq htarget)
end
export P.D23 (pair_coordinate_cardinality_loss_absorbed_by_beta_shift)

end

open MatrixCompletion P

lemma shifted_bernstein_scale (C e f beta L p : ℝ)
    (hC : 0 ≤ C) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hbeta : 2 < beta) (hL : 0 ≤ L) (hp : 0 ≤ p) :
    C * (Real.sqrt (((beta + 4) * L) / p) * f +
      (((beta + 4) * L) / p) * e) ≤
    (3 * C) * (Real.sqrt ((beta * L) / p) * f +
      ((beta * L) / p) * e) := by
  have hbase : 0 ≤ beta * L / p := div_nonneg (mul_nonneg (by linarith) hL) hp
  have hratio : (beta + 4) * L / p ≤ 3 * (beta * L / p) := by
    calc
      (beta + 4) * L / p ≤ (3 * beta) * L / p :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by linarith) hL) hp
      _ = 3 * (beta * L / p) := by ring
  have hroot : Real.sqrt (((beta + 4) * L) / p) ≤
      3 * Real.sqrt ((beta * L) / p) := by
    calc
      Real.sqrt (((beta + 4) * L) / p) ≤ Real.sqrt (9 * (beta * L / p)) :=
        Real.sqrt_le_sqrt (hratio.trans (by linarith))
      _ = 3 * Real.sqrt ((beta * L) / p) := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9)]
        norm_num
  calc
    C * (Real.sqrt (((beta + 4) * L) / p) * f +
        (((beta + 4) * L) / p) * e) ≤
        C * ((3 * Real.sqrt ((beta * L) / p)) * f +
          (3 * (beta * L / p)) * e) :=
      mul_le_mul_of_nonneg_left
        (add_le_add (mul_le_mul_of_nonneg_right hroot hf)
          (mul_le_mul_of_nonneg_right hratio he)) hC
    _ = (3 * C) * (Real.sqrt ((beta * L) / p) * f +
        ((beta * L) / p) * e) := by ring

open P.D19.Bot5_minpoint

set_option maxHeartbeats 2000000 in
theorem linear_density_scale_absorption
    (Cbern Centry Cfro : ℝ) (hCbern : 0 < Cbern) (hCentry : 0 < Centry) (hCfro : 0 < Cfro)
    (β : ℝ) (hβ : 2 < β)
    (n₁ n₂ r m : ℕ) (μ₀ : ℝ)
    (hn1 : 0 < n₁) (hn2 : 0 < n₂) (hr : 0 < r) (hm : m ≤ n₁ * n₂)
    (hμ0 : 1 ≤ μ₀)
    (hmaxge2 : (2:ℝ) ≤ (↑(max n₁ n₂) : ℝ))
    (hdens : (m : ℝ) ≥ μ₀ * (↑(max n₁ n₂)) * (r : ℝ) *
      (β * Real.log (↑(max n₁ n₂)))) :
    Cbern *
        (Real.sqrt
            ((β * Real.log (↑(max n₁ n₂))) /
              ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) *
            Real.rpow ((r : ℝ) / (↑(min n₁ n₂))) ((3 : ℝ) / 2)) +
          ((β * Real.log (↑(max n₁ n₂))) /
            ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
          (Centry * μ₀ ^ 2 *
            (((r : ℝ) / (↑(min n₁ n₂))) ^ 2))) ≤
      (Cbern * (Cfro + Centry)) *
        Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
          Real.rpow
            ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ))
            ((3 : ℝ) / 2) := by

  set X : ℝ := (↑(max n₁ n₂) : ℝ) with hX
  set Y : ℝ := (↑(min n₁ n₂) : ℝ) with hY
  set L : ℝ := β * Real.log X with hL
  have hμ0pos : 0 < μ₀ := by linarith
  have hrR : (1:ℝ) ≤ (r:ℝ) := by exact_mod_cast hr
  have hrpos : 0 < (r:ℝ) := by linarith
  have hXpos : 0 < X := by linarith
  have hYpos : 0 < Y := by rw [hY]; have : 0 < min n₁ n₂ := lt_min hn1 hn2; exact_mod_cast this
  have hn1R : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast hn1
  have hn2R : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast hn2
  have hLpos : 0 < L := by
    rw [hL]; have := beta_log_ge_one β hβ X hmaxge2; linarith
  have hDpos : 0 < μ₀ * X * (r : ℝ) * L := by positivity
  have hmR : (0 : ℝ) < (m : ℝ) := lt_of_lt_of_le hDpos hdens

  have hminmax : Y * X = (n₁:ℝ) * (n₂:ℝ) := by rw [hY, hX]; exact min_mul_max_real n₁ n₂
  have hmle : (m:ℝ) ≤ (n₁:ℝ) * (n₂:ℝ) := by exact_mod_cast hm
  have hmleXY : (m:ℝ) ≤ X * Y := by rw [mul_comm]; exact le_trans hmle (le_of_eq hminmax.symm)

  set p : ℝ := (m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)) with hp
  have hppos : 0 < p := by rw [hp]; positivity
  have hple1 : p ≤ 1 := by rw [hp, div_le_one (by positivity)]; exact hmle
  have hpinv : p⁻¹ = X * Y / (m:ℝ) := by
    rw [hp, inv_div, ← hminmax]; ring
  have hYbound : μ₀ * (r : ℝ) * L ≤ Y := by
    have hchain : μ₀ * X * (r : ℝ) * L ≤ X * Y := hdens.trans hmleXY
    apply (mul_le_mul_iff_right₀ hXpos).mp
    calc X * (μ₀ * (r : ℝ) * L) = μ₀ * X * (r : ℝ) * L := by ring
      _ ≤ X * Y := hchain

  set q : ℝ := μ₀ * X * (r:ℝ) / (m:ℝ) with hq
  have hqpos : 0 < q := by rw [hq]; positivity
  set S : ℝ := Real.rpow q ((3:ℝ)/2) with hS
  have hSpos : 0 < S := by rw [hS]; exact Real.rpow_pos_of_pos hqpos _
  have hsqrtL : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos

  have hT1 : Real.sqrt (L / p) *
      (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) * Real.rpow ((r:ℝ) / Y) ((3 : ℝ) / 2))
        ≤ Cfro * (Real.sqrt L * S) := by

    have hrpμ : 0 ≤ Real.rpow μ₀ ((3:ℝ)/2) := Real.rpow_nonneg (le_of_lt hμ0pos) _
    have hrprY : 0 ≤ Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2) := Real.rpow_nonneg (by positivity) _
    have hinner_nn : 0 ≤ Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2) :=
      mul_nonneg hrpμ hrprY

    rw [show Cfro * Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2)
          = Cfro * (Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2)) by ring,
        show Real.sqrt (L/p) * (Cfro * (Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2)))
          = Cfro * (Real.sqrt (L/p) * (Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2))) by ring]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hCfro)

    have hLHS_nn : 0 ≤ Real.sqrt (L/p) * (Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2)) :=
      mul_nonneg (Real.sqrt_nonneg _) hinner_nn
    have hRHS_nn : 0 ≤ Real.sqrt L * S := by positivity
    rw [← Real.sqrt_sq hRHS_nn, ← Real.sqrt_sq hLHS_nn]
    apply Real.sqrt_le_sqrt

    have he_lhs : (Real.sqrt (L/p) * (Real.rpow μ₀ ((3:ℝ)/2) * Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2)))^2
        = (L/p) * (μ₀^3 * ((r:ℝ)/Y)^3) := by
      rw [mul_pow, Real.sq_sqrt (by positivity)]
      rw [mul_pow]
      rw [show (Real.rpow μ₀ ((3:ℝ)/2))^2 = μ₀^3 by
            rw [rpow_three_half μ₀ (le_of_lt hμ0pos)]; rw [mul_pow, Real.sq_sqrt (le_of_lt hμ0pos)]; ring,
          show (Real.rpow ((r:ℝ)/Y) ((3:ℝ)/2))^2 = ((r:ℝ)/Y)^3 by
            rw [rpow_three_half ((r:ℝ)/Y) (by positivity)]; rw [mul_pow, Real.sq_sqrt (by positivity)]; ring]
    have he_rhs : (Real.sqrt L * S)^2 = L * q^3 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hLpos), hS]
      rw [show (Real.rpow q ((3:ℝ)/2))^2 = q^3 by
            rw [rpow_three_half q (le_of_lt hqpos)]; rw [mul_pow, Real.sq_sqrt (le_of_lt hqpos)]; ring]
    rw [he_lhs, he_rhs, hq]

    have key : μ₀^3 * ((r:ℝ)/Y)^3 ≤ (μ₀ * X * (r:ℝ)/(m:ℝ))^3 * p := by
      have hpval : p = (m:ℝ) / (X * Y) := by
        rw [hp, ← hminmax]; rw [mul_comm Y X]
      rw [hpval]
      have hmsq : (m:ℝ)^2 ≤ X^2 * Y^2 := by
        rw [← mul_pow]; exact pow_le_pow_left₀ hmR.le hmleXY 2

      have hlhs_eq : μ₀^3 * ((r:ℝ)/Y)^3 = (μ₀^3 * (r:ℝ)^3) / Y^3 := by
        rw [div_pow]; ring
      have hrhs_eq : (μ₀ * X * (r:ℝ)/(m:ℝ))^3 * ((m:ℝ)/(X*Y))
          = (μ₀^3 * X^2 * (r:ℝ)^3) / ((m:ℝ)^2 * Y) := by
        rw [div_pow]; field_simp
      rw [hlhs_eq, hrhs_eq]
      rw [div_le_div_iff₀ (by positivity) (by positivity)]

      have hfac : 0 ≤ μ₀^3 * (r:ℝ)^3 * Y :=
        le_of_lt (mul_pos (mul_pos (pow_pos hμ0pos 3) (pow_pos hrpos 3)) hYpos)
      linarith [mul_le_mul_of_nonneg_left hmsq hfac]
    have hLp : L / p = L * p⁻¹ := by rw [div_eq_mul_inv]
    rw [hLp]
    calc L * p⁻¹ * (μ₀^3 * ((r:ℝ)/Y)^3)
        ≤ L * p⁻¹ * ((μ₀ * X * (r:ℝ)/(m:ℝ))^3 * p) := by
          apply mul_le_mul_of_nonneg_left key (by positivity)
      _ = L * (μ₀ * X * (r:ℝ)/(m:ℝ))^3 := by
          have : p⁻¹ * p = 1 := inv_mul_cancel₀ (ne_of_gt hppos)
          field_simp

  have hT2 : (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2))
        ≤ Centry * (Real.sqrt L * S) := by
    rw [show Centry * μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2)
          = Centry * (μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2)) by ring,
        show (L / p) * (Centry * (μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2)))
          = Centry * ((L / p) * (μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2))) by ring]
    apply mul_le_mul_of_nonneg_left _ (le_of_lt hCentry)

    have hLHS_nn : 0 ≤ (L / p) * (μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2)) := by positivity
    have hRHS_nn : 0 ≤ Real.sqrt L * S := by positivity
    rw [← Real.sqrt_sq hRHS_nn, ← Real.sqrt_sq hLHS_nn]
    apply Real.sqrt_le_sqrt

    have he_rhs : (Real.sqrt L * S)^2 = L * q^3 := by
      rw [mul_pow, Real.sq_sqrt (le_of_lt hLpos), hS]
      rw [show (Real.rpow q ((3:ℝ)/2))^2 = q^3 by
            rw [rpow_three_half q (le_of_lt hqpos)]; rw [mul_pow, Real.sq_sqrt (le_of_lt hqpos)]; ring]
    rw [he_rhs, hq]

    have hpval : (1:ℝ)/p = X * Y / (m:ℝ) := by rw [one_div]; exact hpinv
    have hLHS_eq : ((L / p) * (μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2)))^2
        = L^2 * (X*Y/(m:ℝ))^2 * (μ₀^4 * (r:ℝ)^4 / Y^4) := by
      rw [div_eq_mul_inv L p, ← one_div, hpval]
      rw [div_pow]
      ring
    rw [hLHS_eq]

    have hrhs_eq2 : L * (μ₀ * X * (r:ℝ)/(m:ℝ))^3 = L * (μ₀^3 * X^3 * (r:ℝ)^3) / (m:ℝ)^3 := by
      rw [div_pow]; ring
    have hlhs_eq2 : L^2 * (X*Y/(m:ℝ))^2 * (μ₀^4 * (r:ℝ)^4 / Y^4)
        = (L^2 * X^2 * μ₀^4 * (r:ℝ)^4) / ((m:ℝ)^2 * Y^2) := by
      rw [div_pow]; field_simp
    rw [hrhs_eq2, hlhs_eq2]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]

    have hkey2 : L * μ₀ * (r:ℝ) * (m:ℝ) ≤ X * Y^2 := by

      have h1 : L * μ₀ * (r:ℝ) * (m:ℝ) ≤ L * μ₀ * (r:ℝ) * (X * Y) :=
        mul_le_mul_of_nonneg_left hmleXY (by positivity)
      have h2 : L * μ₀ * (r:ℝ) * (X * Y) ≤ Y * (X * Y) := by
        have hYb : μ₀ * (r:ℝ) * L ≤ Y := hYbound
        have : L * μ₀ * (r:ℝ) ≤ Y := by rw [show L * μ₀ * (r:ℝ) = μ₀ * (r:ℝ) * L by ring]; exact hYb
        apply mul_le_mul_of_nonneg_right this (by positivity)
      calc L * μ₀ * (r:ℝ) * (m:ℝ) ≤ L * μ₀ * (r:ℝ) * (X * Y) := h1
        _ ≤ Y * (X * Y) := h2
        _ = X * Y^2 := by ring

    have hfac2 : 0 ≤ L * μ₀^3 * X^2 * (r:ℝ)^3 * (m:ℝ)^2 := by positivity
    linarith [mul_le_mul_of_nonneg_left hkey2 hfac2]

  have hsum : Real.sqrt (L / p) *
        (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) * Real.rpow ((r:ℝ) / Y) ((3 : ℝ) / 2)) +
      (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2))
        ≤ (Cfro + Centry) * (Real.sqrt L * S) := by
    have := add_le_add hT1 hT2
    calc Real.sqrt (L / p) *
          (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) * Real.rpow ((r:ℝ) / Y) ((3 : ℝ) / 2)) +
        (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2))
          ≤ Cfro * (Real.sqrt L * S) + Centry * (Real.sqrt L * S) := this
      _ = (Cfro + Centry) * (Real.sqrt L * S) := by ring

  have hgoal_lhs : Cbern *
      (Real.sqrt ((β * Real.log (↑(max n₁ n₂))) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) * Real.rpow ((r : ℝ) / (↑(min n₁ n₂))) ((3 : ℝ) / 2)) +
        ((β * Real.log (↑(max n₁ n₂))) / ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))) *
        (Centry * μ₀ ^ 2 * (((r : ℝ) / (↑(min n₁ n₂))) ^ 2)))
      = Cbern * (Real.sqrt (L / p) *
        (Cfro * Real.rpow μ₀ ((3 : ℝ) / 2) * Real.rpow ((r:ℝ) / Y) ((3 : ℝ) / 2)) +
      (L / p) * (Centry * μ₀ ^ 2 * (((r:ℝ) / Y) ^ 2))) := by
    rw [← hX, ← hY, ← hL, ← hp]
  rw [hgoal_lhs]
  have hgoal_rhs : (Cbern * (Cfro + Centry)) *
        Real.sqrt (β * Real.log (↑(max n₁ n₂))) *
          Real.rpow ((μ₀ * (↑(max n₁ n₂)) * (r : ℝ)) / (m : ℝ)) ((3 : ℝ) / 2)
      = Cbern * ((Cfro + Centry) * (Real.sqrt L * S)) := by
    rw [← hX, ← hL, ← hq, ← hS]; ring
  rw [hgoal_rhs]
  apply mul_le_mul_of_nonneg_left hsum (le_of_lt hCbern)

theorem solution :
    ∃ Ccoef ccoef : ℝ, 0 < Ccoef ∧ 0 < ccoef ∧
      ∀ C' : ℝ, Ccoef ≤ C' →
      ∀ (β : ℝ), 2 < β →
      ∀ (n₁ n₂ r m : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r → m ≤ n₁ * n₂ →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        (m : ℝ) ≥
          C' * max (max (μ₁ ^ 2) (Real.sqrt μ₀ * μ₁))
                  (μ₀ * Real.rpow (↑(max n₁ n₂)) ((1 : ℝ) / 4))
            * (↑(max n₁ n₂)) * (r : ℝ) *
              (β * Real.log (↑(max n₁ n₂))) →
        bernoulliEventProb ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
            (fun Omega =>
              QuadraticMiddleIndexDistinctMeanCoefficientBound Omega S
                ((m : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ)))
                (let N : ℝ := ↑(max n₁ n₂)
                 let R : ℝ := (r : ℝ)
                 let Mobs : ℝ := (m : ℝ)
                 let logN : ℝ := Real.log N
                 Ccoef * Real.sqrt (β * logN) *
                   Real.rpow ((μ₀ * N * R) / Mobs) ((3 : ℝ) / 2))) ≥
          1 - ccoef * Real.rpow (↑(max n₁ n₂)) (-β) := by
  rcases quadratic_neumann_middle_index_distinct_kernel_square_base_entry_sup_norm_bound_min_dim with
    ⟨Centry, hCentry, hEntry⟩
  rcases quadratic_neumann_middle_index_distinct_kernel_square_base_frobenius_norm_bound_min_dim with
    ⟨Cfro, hCfro, hFrob⟩
  rcases scalar_centered_sampling_bernstein_tail_from_entry_frobenius_scales with
    ⟨Cbern, cbern, hCbern, hcbern, hBernstein⟩
  let Cpoint : ℝ := (3 * Cbern) * (Cfro + Centry)
  have hCpoint : 0 < Cpoint := by dsimp [Cpoint]; positivity
  let Ccoef : ℝ := max Cpoint 1
  have hCcoef : 0 < Ccoef := lt_of_lt_of_le hCpoint (le_max_left _ _)
  refine ⟨Ccoef, cbern + 1, hCcoef, by positivity, ?_⟩
  intro Cprime hCprime beta hbeta n1 n2 r m M mu0 mu1 S
    hn1 hn2 hr hm hmu0 hmu1 hA0 hA1 hsample
  let p : ℝ := (m : ℝ) / ((n1 : ℝ) * (n2 : ℝ))
  let N : ℝ := (max n1 n2 : ℕ)
  let e : ℝ := Centry * mu0 ^ 2 * (((r : ℝ) / (min n1 n2 : ℕ)) ^ 2)
  let f : ℝ := Cfro * Real.rpow mu0 ((3 : ℝ) / 2) *
    Real.rpow ((r : ℝ) / (min n1 n2 : ℕ)) ((3 : ℝ) / 2)
  let scale : ℝ := Real.sqrt (beta * Real.log N) *
    Real.rpow ((mu0 * N * (r : ℝ)) / (m : ℝ)) ((3 : ℝ) / 2)
  have hp : 0 ≤ p ∧ p ≤ 1 := sample_ratio_between_zero_and_one n1 n2 m hn1 hn2 hm
  rcases Nat.lt_or_ge (max n1 n2) 2 with hsmall | hbig
  · have hN1 : max n1 n2 = 1 := by omega
    have hprob := bernoulliEventProb_nonneg p hp.1 hp.2
      (fun Omega => QuadraticMiddleIndexDistinctMeanCoefficientBound Omega S p
        (Ccoef * Real.sqrt (beta * Real.log N) *
          Real.rpow ((mu0 * N * (r : ℝ)) / (m : ℝ)) ((3 : ℝ) / 2)))
    have hpow : Real.rpow N (-beta) = 1 := by
      dsimp only [N]
      rw [hN1]
      simp
    change 1 - (cbern + 1) * Real.rpow N (-beta) ≤ _
    rw [hpow, mul_one]
    exact (by linarith : 1 - (cbern + 1) ≤ 0).trans hprob
  have hN2 : (2 : ℝ) ≤ N := by
    dsimp only [N]
    exact_mod_cast hbig
  have hN : 1 ≤ N := by linarith
  have hlog : 0 ≤ Real.log N := Real.log_nonneg hN
  have hCprime1 : 1 ≤ Cprime := (le_max_right Cpoint 1).trans hCprime
  have hpowN : 1 ≤ Real.rpow N ((1 : ℝ) / 4) := Real.one_le_rpow hN (by norm_num)
  let A : ℝ := max (max (mu1 ^ 2) (Real.sqrt mu0 * mu1))
    (mu0 * Real.rpow N ((1 : ℝ) / 4))
  have hmuA : mu0 ≤ A := by
    have hmu : mu0 ≤ mu0 * Real.rpow N ((1 : ℝ) / 4) := by
      calc mu0 = mu0 * 1 := by ring
        _ ≤ mu0 * Real.rpow N ((1 : ℝ) / 4) :=
          mul_le_mul_of_nonneg_left hpowN (by linarith)
    exact hmu.trans (le_max_right _ _)
  have hA : 0 ≤ A := le_trans (by linarith : 0 ≤ mu0) hmuA
  have hbase : mu0 ≤ Cprime * A := by
    linarith [mul_nonneg (sub_nonneg.mpr hCprime1) hA]
  have hL : 0 ≤ beta * Real.log N := mul_nonneg (by linarith) hlog
  have hlinear : mu0 * N * (r : ℝ) * (beta * Real.log N) ≤ (m : ℝ) :=
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hbase (by linarith)) (Nat.cast_nonneg r)) hL).trans hsample
  have he : 0 ≤ e := by dsimp [e]; positivity
  have hf : 0 ≤ f := by dsimp [f]; positivity
  have hscale :
      Cbern * (Real.sqrt (((beta + 4) * Real.log N) / p) * f +
        (((beta + 4) * Real.log N) / p) * e) ≤ Cpoint * scale := by
    apply le_trans (shifted_bernstein_scale Cbern e f beta (Real.log N) p
      hCbern.le he hf hbeta hlog hp.1)
    simpa only [Cpoint, scale, e, f, p, N, mul_assoc] using
      linear_density_scale_absorption (3 * Cbern) Centry Cfro (by positivity) hCentry hCfro
        beta hbeta n1 n2 r m mu0 hn1 hn2 hr hm hmu0 hN2 hlinear
  have hpoint : ∀ w1 w2 : Fin n1 × Fin n2,
      bernoulliEventProb p
          (fun Omega => |quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1| ≤
            Cpoint * scale) ≥
        1 - cbern * Real.rpow N (-(beta + 4)) := by
    intro w1 _w2
    have hraw := hBernstein (beta + 4) (by linarith) n1 n2 m hn1 hn2 hm
      (fun Omega => quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1)
      (quadraticMiddleIndexDistinctKernelSquareBaseMatrix S w1) e f
      (fun Omega => quadratic_neumann_middle_index_distinct_mean_coefficient_as_centered_scalar_fluctuation
        Omega S p w1)
      (hEntry n1 n2 r M mu0 S hn1 hn2 hr hmu0 hA0 w1)
      (hFrob n1 n2 r M mu0 S hn1 hn2 hr hmu0 hA0 w1)
    apply le_trans hraw
    refine bernoulli_event_probability_mono p _ _ hp.1 hp.2 ?_
    intro Omega hOmega
    exact hOmega.trans hscale
  have hUniform :=
    bernoulli_uniform_coordinate_pair_bound_from_pointwise_tails_with_cardinality_factor
      Cpoint cbern hCpoint hcbern p scale
      (Real.rpow N (-(beta + 4))) hp.1 hp.2 n1 n2
      (fun w1 _w2 Omega => quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1)
      hpoint
  have hcard := pair_coordinate_cardinality_loss_absorbed_by_beta_shift
    beta cbern n1 n2 hbeta hcbern hn1 hn2
  have hMono :
      bernoulliEventProb p
          (fun Omega => ∀ w1 w2 : Fin n1 × Fin n2,
            |quadraticMiddleIndexDistinctMeanCoefficient Omega S p w1| ≤
              Cpoint * scale) ≤
      bernoulliEventProb p
          (fun Omega => QuadraticMiddleIndexDistinctMeanCoefficientBound Omega S p
            (Ccoef * Real.sqrt (beta * Real.log N) *
              Real.rpow ((mu0 * N * (r : ℝ)) / (m : ℝ)) ((3 : ℝ) / 2))) := by
    refine bernoulli_event_probability_mono p _ _ hp.1 hp.2 ?_
    intro Omega hOmega w1
    have hscale0 : 0 ≤ scale := by dsimp [scale]; positivity
    have hbound := (hOmega w1 w1).trans
      (mul_le_mul_of_nonneg_right (le_max_left Cpoint 1) hscale0)
    simpa only [Ccoef, scale, mul_assoc] using hbound
  have hpower : 0 ≤ Real.rpow N (-beta) := Real.rpow_nonneg (by linarith) _
  refine le_trans (le_trans ?_ hUniform) hMono
  dsimp [N] at *
  linarith

#print axioms solution

