-- Prove2me | solution 1 for off_diagonal_tangent_kernel_row_frobenius_bound_from_a0_min
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-26T01:55:07.749446+00:00
-- url     : https://prove2.me/submissions/ffc94fed-0710-413a-b6af-1b54e1f92409

import Definitions.Def_matrix_completion_neumann
open MatrixCompletion
open scoped Classical BigOperators

theorem ptproj_entry {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p : Fin n₁) (q : Fin n₂) (a : Fin n₁) (b : Fin n₂) :
    tangentProjection S (coordinateMatrix p q) a b
      = (if b = q then (∑ k, S.u k a * S.u k p) else 0)
        + (∑ k, S.v k q * S.v k b) * ((if a = p then (1:ℝ) else 0) - (∑ k, S.u k a * S.u k p)) := by
  unfold tangentProjection leftSingularProjection rightSingularProjection
    twoSidedSingularProjection coordinateMatrix
  simp only [Matrix.add_apply, Matrix.sub_apply]
  have hL : (∑ a', (∑ k, S.u k a * S.u k a') * (if a' = p ∧ b = q then (1:ℝ) else 0))
      = if b = q then (∑ k, S.u k a * S.u k p) else 0 := by
    rw [Finset.sum_eq_single p]
    · by_cases hb : b = q <;> simp [hb]
    · intro a' _ ha'; simp [ha']
    · intro h; exact absurd (Finset.mem_univ _) h
  have hR : (∑ b', (if a = p ∧ b' = q then (1:ℝ) else 0) * (∑ k, S.v k b' * S.v k b))
      = (if a = p then (1:ℝ) else 0) * (∑ k, S.v k q * S.v k b) := by
    rw [Finset.sum_eq_single q]
    · by_cases ha : a = p <;> simp [ha]
    · intro b' _ hb'; simp [hb']
    · intro h; exact absurd (Finset.mem_univ _) h
  have hT : (∑ a', ∑ b', (∑ k, S.u k a * S.u k a') * (if a' = p ∧ b' = q then (1:ℝ) else 0) *
        (∑ k, S.v k b' * S.v k b))
      = (∑ k, S.u k a * S.u k p) * (∑ k, S.v k q * S.v k b) := by
    rw [Finset.sum_eq_single p]
    · rw [Finset.sum_eq_single q]
      · simp
      · intro b' _ hb'; simp [hb']
      · intro h; exact absurd (Finset.mem_univ _) h
    · intro a' _ ha'; apply Finset.sum_eq_zero; intro b' _; simp [ha']
    · intro h; exact absurd (Finset.mem_univ _) h
  rw [hL, hR, hT]; ring

theorem pisom {r N : ℕ} (w : Fin r → Fin N → ℝ)
    (horth : ∀ k l, (∑ i, w k i * w l i) = if k = l then 1 else 0) (p : Fin N) :
    (∑ a, (∑ k, w k a * w k p) ^ 2) = ∑ k, (w k p) ^ 2 := by
  have expand : (∑ a, (∑ k, w k a * w k p) ^ 2)
      = ∑ a, ∑ k, ∑ l, (w k a * w k p) * (w l a * w l p) := by
    apply Finset.sum_congr rfl; intro a _
    rw [sq, Finset.sum_mul_sum]
  rw [expand, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun (k : Fin r) _ => Finset.sum_comm)]
  have step : ∀ k l : Fin r,
      (∑ a, (w k a * w k p) * (w l a * w l p)) = (w k p * w l p) * (∑ a, w k a * w l a) := by
    intro k l; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  simp only [step, horth]
  apply Finset.sum_congr rfl; intro k _
  rw [Finset.sum_eq_single k]
  · simp [sq]
  · intro l _ hl; simp only [if_neg (Ne.symm hl), mul_zero]
  · intro h; exact absurd (Finset.mem_univ _) h

theorem frob_eq {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (p : Fin n₁) (q : Fin n₂) :
    frobeniusNormSq (tangentProjection S (coordinateMatrix p q))
      = (∑ k, (S.u k p)^2) + (∑ k, (S.v k q)^2)
        - (∑ k, (S.u k p)^2) * (∑ k, (S.v k q)^2) := by
  have hPUp : (∑ k, S.u k p * S.u k p) = ∑ k, (S.u k p)^2 := by
    apply Finset.sum_congr rfl; intro k _; rw [sq]
  have hsumPUsq : (∑ i, (∑ k, S.u k i * S.u k p)^2) = ∑ k, (S.u k p)^2 :=
    pisom S.u S.u_orthonormal p
  have hsumPVsq : (∑ j, (∑ k, S.v k q * S.v k j)^2) = ∑ k, (S.v k q)^2 := by
    rw [← pisom S.v S.v_orthonormal q]
    apply Finset.sum_congr rfl; intro j _
    congr 1; apply Finset.sum_congr rfl; intro k _; ring
  unfold frobeniusNormSq
  simp only [ptproj_entry S p q]
  -- split each square (A+B)^2 = A^2 + 2 A B + B^2
  rw [show (∑ i, ∑ j,
        ((if j = q then (∑ k, S.u k i * S.u k p) else 0)
          + (∑ k, S.v k q * S.v k j) * ((if i = p then (1:ℝ) else 0) - (∑ k, S.u k i * S.u k p)))^2)
      = (∑ i, ∑ j, (if j = q then (∑ k, S.u k i * S.u k p) else 0)^2)
        + (∑ i, ∑ j, 2 * ((if j = q then (∑ k, S.u k i * S.u k p) else 0)
              * ((∑ k, S.v k q * S.v k j) * ((if i = p then (1:ℝ) else 0) - (∑ k, S.u k i * S.u k p)))))
        + (∑ i, ∑ j, ((∑ k, S.v k q * S.v k j) * ((if i = p then (1:ℝ) else 0) - (∑ k, S.u k i * S.u k p)))^2)
      from by
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro j _; ring]
  -- S1 = α
  have hS1 : (∑ i, ∑ j, (if j = q then (∑ k, S.u k i * S.u k p) else 0)^2) = ∑ k, (S.u k p)^2 := by
    rw [← hsumPUsq]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_eq_single q]
    · simp
    · intro j _ hj; simp [hj]
    · intro h; exact absurd (Finset.mem_univ _) h
  -- S2 = 0
  have hS2 : (∑ i, ∑ j, 2 * ((if j = q then (∑ k, S.u k i * S.u k p) else 0)
        * ((∑ k, S.v k q * S.v k j) * ((if i = p then (1:ℝ) else 0) - (∑ k, S.u k i * S.u k p))))) = 0 := by
    have hinner : ∀ i : Fin n₁,
        (∑ j, 2 * ((if j = q then (∑ k, S.u k i * S.u k p) else 0)
          * ((∑ k, S.v k q * S.v k j) * ((if i = p then (1:ℝ) else 0) - (∑ k, S.u k i * S.u k p)))))
        = (∑ k, S.v k q * S.v k q) * (2 * ((∑ k, S.u k i * S.u k p) *
            ((if i = p then (1:ℝ) else 0) - (∑ k, S.u k i * S.u k p)))) := by
      intro i
      rw [Finset.sum_eq_single q]
      · simp; ring
      · intro j _ hj; simp [hj]
      · intro h; exact absurd (Finset.mem_univ _) h
    rw [Finset.sum_congr rfl (fun i _ => hinner i)]
    rw [← Finset.mul_sum]
    have : (∑ i, 2 * ((∑ k, S.u k i * S.u k p) * ((if i = p then (1:ℝ) else 0) - (∑ k, S.u k i * S.u k p)))) = 0 := by
      have he : (∑ i, 2 * ((∑ k, S.u k i * S.u k p) * ((if i = p then (1:ℝ) else 0) - (∑ k, S.u k i * S.u k p))))
          = 2 * ((∑ i, (∑ k, S.u k i * S.u k p) * (if i = p then (1:ℝ) else 0)) - (∑ i, (∑ k, S.u k i * S.u k p)^2)) := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [he]
      have h1 : (∑ i, (∑ k, S.u k i * S.u k p) * (if i = p then (1:ℝ) else 0)) = ∑ k, (S.u k p)^2 := by
        rw [Finset.sum_eq_single p]
        · simp [hPUp]
        · intro i _ hi; simp [hi]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [h1, hsumPUsq]; ring
    rw [this, mul_zero]
  -- S3 = β - α β
  have hS3 : (∑ i, ∑ j, ((∑ k, S.v k q * S.v k j) * ((if i = p then (1:ℝ) else 0) - (∑ k, S.u k i * S.u k p)))^2)
      = (∑ k, (S.v k q)^2) - (∑ k, (S.u k p)^2) * (∑ k, (S.v k q)^2) := by
    have hinner : ∀ i : Fin n₁,
        (∑ j, ((∑ k, S.v k q * S.v k j) * ((if i = p then (1:ℝ) else 0) - (∑ k, S.u k i * S.u k p)))^2)
        = ((if i = p then (1:ℝ) else 0) - (∑ k, S.u k i * S.u k p))^2 * (∑ k, (S.v k q)^2) := by
      intro i
      rw [← hsumPVsq, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro j _; ring
    rw [Finset.sum_congr rfl (fun i _ => hinner i)]
    rw [← Finset.sum_mul]
    have hsum : (∑ i, ((if i = p then (1:ℝ) else 0) - (∑ k, S.u k i * S.u k p))^2) = 1 - (∑ k, (S.u k p)^2) := by
      have he : (∑ i, ((if i = p then (1:ℝ) else 0) - (∑ k, S.u k i * S.u k p))^2)
          = (∑ i, (if i = p then (1:ℝ) else 0)^2) - 2 * (∑ i, (if i = p then (1:ℝ) else 0) * (∑ k, S.u k i * S.u k p))
            + (∑ i, (∑ k, S.u k i * S.u k p)^2) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro i _; ring
      rw [he, hsumPUsq]
      have h1 : (∑ i, (if i = p then (1:ℝ) else 0)^2) = 1 := by
        rw [Finset.sum_eq_single p]
        · simp
        · intro i _ hi; simp [hi]
        · intro h; exact absurd (Finset.mem_univ _) h
      have h2 : (∑ i, (if i = p then (1:ℝ) else 0) * (∑ k, S.u k i * S.u k p)) = ∑ k, (S.u k p)^2 := by
        rw [Finset.sum_eq_single p]
        · simp [hPUp]
        · intro i _ hi; simp [hi]
        · intro h; exact absurd (Finset.mem_univ _) h
      rw [h1, h2]; ring
    rw [hsum]; ring
  rw [hS1, hS2, hS3]; ring

theorem matrixInner_coord {n₁ n₂ : ℕ} (X : RealMatrix n₁ n₂) (a : Fin n₁) (b : Fin n₂) :
    matrixInner X (coordinateMatrix a b) = X a b := by
  unfold matrixInner coordinateMatrix
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'; simp [hb']
    · intro h; exact absurd (Finset.mem_univ _) h
  · intro a' _ ha'; apply Finset.sum_eq_zero; intro b' _; simp [ha']
  · intro h; exact absurd (Finset.mem_univ _) h

theorem kernel_symm {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (i : Fin n₁) (j : Fin n₂) (a : Fin n₁) (b : Fin n₂) :
    tangentCoordinateKernel S i j a b = tangentCoordinateKernel S a b i j := by
  unfold tangentCoordinateKernel
  rw [matrixInner_coord, matrixInner_coord, ptproj_entry S i j a b, ptproj_entry S a b i j]
  have e1 : (∑ k, S.u k a * S.u k i) = (∑ k, S.u k i * S.u k a) := by
    apply Finset.sum_congr rfl; intro k _; ring
  have e2 : (∑ k, S.v k j * S.v k b) = (∑ k, S.v k b * S.v k j) := by
    apply Finset.sum_congr rfl; intro k _; ring
  rw [e1, e2]
  by_cases hbj : b = j
  · by_cases hai : a = i
    · rw [if_pos hbj, if_pos hbj.symm, if_pos hai, if_pos hai.symm]
    · rw [if_pos hbj, if_pos hbj.symm, if_neg hai, if_neg (Ne.symm hai)]
  · by_cases hai : a = i
    · rw [if_neg hbj, if_neg (Ne.symm hbj), if_pos hai, if_pos hai.symm]
    · rw [if_neg hbj, if_neg (Ne.symm hbj), if_neg hai, if_neg (Ne.symm hai)]

theorem full_kernel_sum {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ} (S : SVD M r)
    (a : Fin n₁) (b : Fin n₂) :
    (∑ i, ∑ j, (tangentCoordinateKernel S i j a b) ^ 2)
      = frobeniusNormSq (tangentProjection S (coordinateMatrix a b)) := by
  unfold frobeniusNormSq
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  rw [kernel_symm S i j a b]
  unfold tangentCoordinateKernel
  rw [matrixInner_coord]

theorem solution :
    ∃ Cker : ℝ, 0 < Cker ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → A0 S μ₀ →
        ∀ w : Fin n₁ × Fin n₂,
          frobeniusNorm
              (fun i j =>
                if (i, j) = w then 0
                else tangentCoordinateKernel S i j w.1 w.2) ≤
            Cker * Real.sqrt
              (μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := by
  refine ⟨Real.sqrt 2, by positivity, ?_⟩
  intro n₁ n₂ r M μ₀ S hn1 hn2 hr hμ0 hA0 w
  simp only [Nat.cast_min]
  have hcoh : ∀ (N rr : ℕ) (wv : Fin rr → Fin N → ℝ), 0 < N → 0 < rr →
      coherence N rr wv ≤ μ₀ → ∀ pp : Fin N, (∑ k, (wv k pp)^2) ≤ μ₀ * rr / N := by
    intro N rr wv hN hrr hcohle pp
    unfold coherence at hcohle
    have hbdd : BddAbove (Set.range (fun i => ∑ k, (wv k i)^2)) :=
      Set.Finite.bddAbove (Set.finite_range _)
    have hle : (∑ k, (wv k pp)^2) ≤ ⨆ i, ∑ k, (wv k i)^2 := le_ciSup hbdd pp
    have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
    have hrrpos : (0:ℝ) < (rr:ℝ) := by exact_mod_cast hrr
    have hNr : (0:ℝ) < (N:ℝ)/(rr:ℝ) := by positivity
    have hsup : (⨆ i, ∑ k, (wv k i)^2) ≤ μ₀ / ((N:ℝ)/(rr:ℝ)) := by
      rw [le_div_iff₀ hNr, mul_comm]; exact hcohle
    have heq : μ₀ / ((N:ℝ)/(rr:ℝ)) = μ₀ * rr / N := by field_simp
    rw [heq] at hsup
    exact le_trans hle hsup
  have hμr : 0 ≤ μ₀ * (r:ℝ) := mul_nonneg (by linarith) (by positivity)
  have hα : (∑ k, (S.u k w.1)^2) ≤ μ₀ * r / n₁ := hcoh n₁ r S.u hn1 hr hA0.1 w.1
  have hβ : (∑ k, (S.v k w.2)^2) ≤ μ₀ * r / n₂ := hcoh n₂ r S.v hn2 hr hA0.2 w.2
  have hα0 : 0 ≤ (∑ k, (S.u k w.1)^2) := by positivity
  have hβ0 : 0 ≤ (∑ k, (S.v k w.2)^2) := by positivity
  have hminpos : (0:ℝ) < (min n₁ n₂ : ℝ) := by
    have : 0 < min n₁ n₂ := lt_min hn1 hn2
    exact_mod_cast this
  have hb1 : μ₀ * r / (n₁:ℝ) ≤ μ₀ * r / (min n₁ n₂ : ℝ) := by
    gcongr
    exact_mod_cast min_le_left n₁ n₂
  have hb2 : μ₀ * r / (n₂:ℝ) ≤ μ₀ * r / (min n₁ n₂ : ℝ) := by
    gcongr
    exact_mod_cast min_le_right n₁ n₂
  have hab : 0 ≤ (∑ k, (S.u k w.1)^2) * (∑ k, (S.v k w.2)^2) := mul_nonneg hα0 hβ0
  have hD_le : frobeniusNormSq (tangentProjection S (coordinateMatrix w.1 w.2))
      ≤ 2 * (μ₀ * ((r:ℝ) / (min n₁ n₂ : ℝ))) := by
    rw [frob_eq]
    have h2 : 2 * (μ₀ * ((r:ℝ) / (min n₁ n₂ : ℝ)))
        = μ₀ * r / (min n₁ n₂ : ℝ) + μ₀ * r / (min n₁ n₂ : ℝ) := by ring
    rw [h2]; linarith [hα, hβ, hb1, hb2, hab]
  have hfsq_le : frobeniusNormSq
        (fun i j => if (i, j) = w then 0 else tangentCoordinateKernel S i j w.1 w.2)
      ≤ frobeniusNormSq (tangentProjection S (coordinateMatrix w.1 w.2)) := by
    rw [← full_kernel_sum S w.1 w.2]
    unfold frobeniusNormSq
    apply Finset.sum_le_sum; intro i _
    apply Finset.sum_le_sum; intro j _
    show (if (i, j) = w then (0:ℝ) else tangentCoordinateKernel S i j w.1 w.2) ^ 2
        ≤ (tangentCoordinateKernel S i j w.1 w.2) ^ 2
    split_ifs with h
    · simpa using sq_nonneg (tangentCoordinateKernel S i j w.1 w.2)
    · exact le_refl _
  have hcombine : frobeniusNormSq
        (fun i j => if (i, j) = w then 0 else tangentCoordinateKernel S i j w.1 w.2)
      ≤ 2 * (μ₀ * ((r:ℝ) / (min n₁ n₂ : ℝ))) := le_trans hfsq_le hD_le
  unfold frobeniusNorm
  calc Real.sqrt (frobeniusNormSq
          (fun i j => if (i, j) = w then 0 else tangentCoordinateKernel S i j w.1 w.2))
      ≤ Real.sqrt (2 * (μ₀ * ((r:ℝ) / (min n₁ n₂ : ℝ)))) := Real.sqrt_le_sqrt hcombine
    _ = Real.sqrt 2 * Real.sqrt (μ₀ * ((r:ℝ) / (min n₁ n₂ : ℝ))) :=
        Real.sqrt_mul (by norm_num) _
