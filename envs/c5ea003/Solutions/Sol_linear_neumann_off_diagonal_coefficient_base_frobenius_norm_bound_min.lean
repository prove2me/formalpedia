-- Prove2me | solution 1 for linear_neumann_off_diagonal_coefficient_base_frobenius_norm_bound_min
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-06-26T02:03:27.234033+00:00
-- url     : https://prove2.me/submissions/4796b9b3-c4da-4c78-bfc1-2bcda894ff8a

import Definitions.Def_linear_neumann_offdiag_bernstein
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
    ∃ Cfro : ℝ, 0 < Cfro ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ μ₁ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → 1 ≤ μ₁ →
        A0 S μ₀ → A1 S μ₁ →
        ∀ w : Fin n₁ × Fin n₂,
          frobeniusNorm
              (linearNeumannOffDiagonalCoefficientBaseMatrix S w) ≤
            Cfro * μ₁ *
              Real.sqrt ((r : ℝ) / ((n₁ : ℝ) * (n₂ : ℝ))) *
                Real.sqrt (μ₀ * ((r : ℝ) / (↑(min n₁ n₂)))) := by
  refine ⟨Real.sqrt 2, by positivity, ?_⟩
  intro n₁ n₂ r M μ₀ μ₁ S hn1 hn2 hr hμ0 hμ1 hA0 hA1 w
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
  set X : ℝ := (r:ℝ) / ((n₁:ℝ) * (n₂:ℝ)) with hXdef
  set Y : ℝ := μ₀ * ((r:ℝ) / (min (n₁:ℝ) (n₂:ℝ))) with hYdef
  have hX0 : 0 ≤ X := by rw [hXdef]; positivity
  have hY0 : 0 ≤ Y := by rw [hYdef]; positivity
  have hD_le : frobeniusNormSq (tangentProjection S (coordinateMatrix w.1 w.2)) ≤ 2 * Y := by
    rw [frob_eq, hYdef]
    have h2 : 2 * (μ₀ * ((r:ℝ) / (min (n₁:ℝ) (n₂:ℝ))))
        = μ₀ * r / (min n₁ n₂ : ℝ) + μ₀ * r / (min n₁ n₂ : ℝ) := by
      push_cast; ring
    rw [h2]; linarith [hα, hβ, hb1, hb2, hab]
  -- frobeniusNormSq B ≤ μ₁²·X·D
  have hAns : frobeniusNormSq (linearNeumannOffDiagonalCoefficientBaseMatrix S w)
      ≤ μ₁ ^ 2 * X * frobeniusNormSq (tangentProjection S (coordinateMatrix w.1 w.2)) := by
    rw [← full_kernel_sum S w.1 w.2]
    unfold frobeniusNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro j _
    show (if (i, j) = w then (0:ℝ)
            else signMatrix S i j * tangentCoordinateKernel S i j w.1 w.2) ^ 2
        ≤ μ₁ ^ 2 * X * (tangentCoordinateKernel S i j w.1 w.2) ^ 2
    have hE2 : (signMatrix S i j) ^ 2 ≤ μ₁ ^ 2 * X := by
      have h := hA1 i j
      have hsq : (signMatrix S i j) ^ 2 ≤ (μ₁ * Real.sqrt X) ^ 2 := by
        rw [← sq_abs (signMatrix S i j)]
        exact pow_le_pow_left₀ (abs_nonneg _) h 2
      rw [mul_pow, Real.sq_sqrt hX0] at hsq; exact hsq
    split_ifs with h
    · rw [show (0:ℝ) ^ 2 = 0 from by norm_num]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) hX0) (sq_nonneg _)
    · rw [mul_pow]
      exact mul_le_mul_of_nonneg_right hE2 (sq_nonneg _)
  have key : frobeniusNormSq (linearNeumannOffDiagonalCoefficientBaseMatrix S w)
      ≤ 2 * μ₁ ^ 2 * X * Y := by
    have hμ1X0 : 0 ≤ μ₁ ^ 2 * X := by positivity
    calc frobeniusNormSq (linearNeumannOffDiagonalCoefficientBaseMatrix S w)
        ≤ μ₁ ^ 2 * X * frobeniusNormSq (tangentProjection S (coordinateMatrix w.1 w.2)) := hAns
      _ ≤ μ₁ ^ 2 * X * (2 * Y) := mul_le_mul_of_nonneg_left hD_le hμ1X0
      _ = 2 * μ₁ ^ 2 * X * Y := by ring
  unfold frobeniusNorm
  have hrhs_nonneg : 0 ≤ Real.sqrt 2 * μ₁ * Real.sqrt X * Real.sqrt Y := by positivity
  have hrhs_sq : (Real.sqrt 2 * μ₁ * Real.sqrt X * Real.sqrt Y) ^ 2 = 2 * μ₁ ^ 2 * X * Y := by
    rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2),
      Real.sq_sqrt hX0, Real.sq_sqrt hY0]
  have hle2 : frobeniusNormSq (linearNeumannOffDiagonalCoefficientBaseMatrix S w)
      ≤ (Real.sqrt 2 * μ₁ * Real.sqrt X * Real.sqrt Y) ^ 2 := by rw [hrhs_sq]; exact key
  calc Real.sqrt (frobeniusNormSq (linearNeumannOffDiagonalCoefficientBaseMatrix S w))
      ≤ Real.sqrt ((Real.sqrt 2 * μ₁ * Real.sqrt X * Real.sqrt Y) ^ 2) := Real.sqrt_le_sqrt hle2
    _ = Real.sqrt 2 * μ₁ * Real.sqrt X * Real.sqrt Y := Real.sqrt_sq hrhs_nonneg
