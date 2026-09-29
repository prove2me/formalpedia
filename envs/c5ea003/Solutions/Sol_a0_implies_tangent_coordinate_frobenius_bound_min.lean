-- Prove2me | solution 1 for a0_implies_tangent_coordinate_frobenius_bound_min
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-06-21T04:59:47.943289+00:00
-- url     : https://prove2.me/submissions/f8d10e15-6264-4cf6-9a5c-7869bd717771

import Definitions.Def_matrix_completion_tangent
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

open MatrixCompletion
open scoped Classical BigOperators

namespace MatrixCompletion

/-- Idempotence of the symmetric projector kernel built from an orthonormal family. -/
theorem ker_idem' {N r : Nat} (u : Fin r → (Fin N → ℝ))
    (horth : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0)
    (i b : Fin N) :
    (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ k : Fin r, u k i * u k b := by
  have e1 : (∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l b))
      = ∑ a : Fin N, ∑ k : Fin r, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b) := by
    apply Finset.sum_congr rfl; intro a _; rw [Finset.sum_mul_sum]
  rw [e1, Finset.sum_comm]
  have e2 : (∑ k : Fin r, ∑ a : Fin N, ∑ l : Fin r, (u k i * u k a) * (u l a * u l b))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a) := by
    apply Finset.sum_congr rfl; intro k _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro l _
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro a _; ring
  rw [e2]
  have e3 : (∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (∑ a : Fin N, u k a * u l a))
      = ∑ k : Fin r, ∑ l : Fin r, (u k i * u l b) * (if k = l then 1 else 0) := by
    apply Finset.sum_congr rfl; intro k _; apply Finset.sum_congr rfl; intro l _; rw [horth k l]
  rw [e3]
  apply Finset.sum_congr rfl; intro k _
  have : (∑ l : Fin r, u k i * u l b * (if k = l then 1 else 0))
      = ∑ l : Fin r, (if k = l then u k i * u l b else 0) := by
    apply Finset.sum_congr rfl; intro l _; by_cases h : k = l <;> simp [h]
  rw [this, Finset.sum_ite_eq]; simp

/-- The "row energy" α_i = ∑_k u_k(i)^2 = Ku(i,i). -/
noncomputable def rowEnergy {N r : Nat} (u : Fin r → (Fin N → ℝ)) (i : Fin N) : ℝ :=
  ∑ k : Fin r, (u k i)^2

/-- ker idempotence at the diagonal: ∑_a Ku(i,a)^2 = Ku(i,i) = rowEnergy. -/
theorem ker_diag_sq {N r : Nat} (u : Fin r → (Fin N → ℝ))
    (horth : ∀ k l, ∑ i, u k i * u l i = if k = l then 1 else 0)
    (i : Fin N) :
    (∑ a : Fin N, (∑ k : Fin r, u k i * u k a)^2) = rowEnergy u i := by
  have key := ker_idem' u horth i i
  rw [rowEnergy]
  -- key : ∑_a Ku(i,a)·(∑_l u_l a u_l i) = ∑_k u_k i u_k i
  -- Note ∑_l u_l a u_l i = ∑_l u_l i u_l a = Ku(i,a); and ∑_k u_k i u_k i = ∑_k (u_k i)^2
  have e : (∑ a : Fin N, (∑ k : Fin r, u k i * u k a)^2)
      = ∑ a : Fin N, (∑ k : Fin r, u k i * u k a) * (∑ l : Fin r, u l a * u l i) := by
    apply Finset.sum_congr rfl; intro a _
    rw [sq]
    congr 1
    apply Finset.sum_congr rfl; intro l _; ring
  rw [e, key]
  apply Finset.sum_congr rfl; intro k _; rw [sq]

/-- Explicit entries of P_T(e_ij).
    P_T(e_ij)_{p,q} = Ku(p,i)·[q=j] + [p=i]·Kv(j,q) - Ku(p,i)·Kv(j,q). -/
theorem tangent_coord_entry {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (i : Fin n1) (j : Fin n2) (p : Fin n1) (q : Fin n2) :
    tangentProjection S (coordinateMatrix i j) p q
      = (∑ k : Fin r, S.u k p * S.u k i) * (if q = j then (1:ℝ) else 0)
        + (if p = i then (1:ℝ) else 0) * (∑ l : Fin r, S.v l j * S.v l q)
        - (∑ k : Fin r, S.u k p * S.u k i) * (∑ l : Fin r, S.v l j * S.v l q) := by
  unfold tangentProjection leftSingularProjection rightSingularProjection
    twoSidedSingularProjection coordinateMatrix
  simp only [Matrix.add_apply, Matrix.sub_apply]
  congr 1
  congr 1
  · -- left: ∑_a Ku(p,a) [a=i ∧ q=j]  = Ku(p,i)·[q=j]
    rw [Finset.sum_eq_single i]
    · by_cases hq : q = j
      · simp [hq]
      · simp [hq]
    · intro a _ ha; simp [ha]
    · intro h; exact absurd (Finset.mem_univ i) h
  · -- right: ∑_b [p=i ∧ b=j] Kv(b,q) = [p=i]·Kv(j,q)
    rw [Finset.sum_eq_single j]
    · by_cases hp : p = i
      · simp [hp]
      · simp [hp]
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  · -- two-sided: ∑_a ∑_b Ku(p,a) [a=i∧b=j] Kv(b,q) = Ku(p,i)·Kv(j,q)
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro b _ hb; simp [hb]
      · intro h; exact absurd (Finset.mem_univ j) h
    · intro a _ ha
      apply Finset.sum_eq_zero; intro b _; simp [ha]
    · intro h; exact absurd (Finset.mem_univ i) h

/-- Frobenius norm squared of P_T(e_ij) equals α + γ - αγ
    where α = rowEnergy u i, γ = rowEnergy v j. -/
theorem tangent_coord_frobSq {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (i : Fin n1) (j : Fin n2) :
    frobeniusNormSq (tangentProjection S (coordinateMatrix i j))
      = rowEnergy S.u i + rowEnergy S.v j
        - rowEnergy S.u i * rowEnergy S.v j := by
  set a : Fin n1 → ℝ := fun p => ∑ k : Fin r, S.u k p * S.u k i with ha
  set c : Fin n2 → ℝ := fun q => ∑ l : Fin r, S.v l j * S.v l q with hc
  -- α = a i, γ = c j
  have haii : a i = rowEnergy S.u i := by
    rw [ha]; simp only; rw [rowEnergy]; apply Finset.sum_congr rfl; intro k _; rw [sq]
  have hcjj : c j = rowEnergy S.v j := by
    rw [hc]; simp only; rw [rowEnergy]; apply Finset.sum_congr rfl; intro l _; rw [sq]
  -- ∑_p (a p)^2 = α
  have hsumA : (∑ p : Fin n1, (a p)^2) = rowEnergy S.u i := by
    have := ker_diag_sq S.u S.u_orthonormal i
    rw [← this]; apply Finset.sum_congr rfl; intro p _; rw [ha]
    simp only; rw [sq, sq, show (∑ k, S.u k i * S.u k p) = ∑ k, S.u k p * S.u k i
      from Finset.sum_congr rfl (fun k _ => by ring)]
  -- ∑_q (c q)^2 = γ
  have hsumC : (∑ q : Fin n2, (c q)^2) = rowEnergy S.v j := by
    have := ker_diag_sq S.v S.v_orthonormal j
    rw [← this]
  -- entries
  have hentry : ∀ p q, tangentProjection S (coordinateMatrix i j) p q
      = a p * (if q = j then (1:ℝ) else 0) + (if p = i then (1:ℝ) else 0) * c q
        - a p * c q := by
    intro p q; rw [tangent_coord_entry S i j p q]
  -- expand frobeniusNormSq
  unfold frobeniusNormSq
  have hpt : (∑ p : Fin n1, ∑ q : Fin n2,
        tangentProjection S (coordinateMatrix i j) p q ^ 2)
      = ∑ p : Fin n1, ∑ q : Fin n2,
        (a p * (if q = j then (1:ℝ) else 0) + (if p = i then (1:ℝ) else 0) * c q
          - a p * c q)^2 := by
    apply Finset.sum_congr rfl; intro p _; apply Finset.sum_congr rfl; intro q _
    rw [hentry p q]
  rw [hpt]
  -- Expand the square into the 6-term separable form (indicators are idempotent):
  -- f^2 = a^2·δ + e·c^2 + a^2 c^2 + 2 a e δ c - 2 a^2 δ c - 2 a e c^2
  have hexpand : ∀ p q,
      (a p * (if q = j then (1:ℝ) else 0) + (if p = i then (1:ℝ) else 0) * c q
        - a p * c q)^2
      = (a p)^2 * (if q = j then (1:ℝ) else 0)
        + (if p = i then (1:ℝ) else 0) * (c q)^2
        + (a p)^2 * (c q)^2
        + 2 * (a p * (if p = i then (1:ℝ) else 0)) * ((if q = j then (1:ℝ) else 0) * c q)
        - 2 * (a p)^2 * ((if q = j then (1:ℝ) else 0) * c q)
        - 2 * (a p * (if p = i then (1:ℝ) else 0)) * (c q)^2 := by
    intro p q
    by_cases hp : p = i <;> by_cases hq : q = j <;> simp [hp, hq] <;> ring
  rw [Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hexpand p q))]
  -- factoring helper: ∑_p ∑_q F p * G q = (∑_p F p) * (∑_q G q)
  have factor : ∀ (F : Fin n1 → ℝ) (G : Fin n2 → ℝ),
      (∑ p : Fin n1, ∑ q : Fin n2, F p * G q) = (∑ p : Fin n1, F p) * (∑ q : Fin n2, G q) := by
    intro F G
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro p _; rw [Finset.mul_sum]
  -- indicator sums
  have sumDelta : (∑ q : Fin n2, (if q = j then (1:ℝ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq']; simp
  have sumE : (∑ p : Fin n1, (if p = i then (1:ℝ) else 0)) = 1 := by
    rw [Finset.sum_ite_eq']; simp
  have sumDeltaC : (∑ q : Fin n2, (if q = j then (1:ℝ) else 0) * c q) = c j := by
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ j) h
  have sumAE : (∑ p : Fin n1, a p * (if p = i then (1:ℝ) else 0)) = a i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ i) h
  -- Split the double sum into 6 separable double-sums.
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  -- now rewrite each of the 6 inner sums into factored products
  -- T1 = ∑∑ (a p)^2 * δ_q
  rw [show (∑ p : Fin n1, ∑ q : Fin n2, (a p)^2 * (if q = j then (1:ℝ) else 0))
        = (∑ p : Fin n1, (a p)^2) * (∑ q : Fin n2, (if q = j then (1:ℝ) else 0))
      from factor (fun p => (a p)^2) (fun q => (if q = j then (1:ℝ) else 0))]
  -- T2 = ∑∑ e_p * (c q)^2
  rw [show (∑ p : Fin n1, ∑ q : Fin n2, (if p = i then (1:ℝ) else 0) * (c q)^2)
        = (∑ p : Fin n1, (if p = i then (1:ℝ) else 0)) * (∑ q : Fin n2, (c q)^2)
      from factor (fun p => (if p = i then (1:ℝ) else 0)) (fun q => (c q)^2)]
  -- T3 = ∑∑ (a p)^2 * (c q)^2
  rw [show (∑ p : Fin n1, ∑ q : Fin n2, (a p)^2 * (c q)^2)
        = (∑ p : Fin n1, (a p)^2) * (∑ q : Fin n2, (c q)^2)
      from factor (fun p => (a p)^2) (fun q => (c q)^2)]
  -- T4 = ∑∑ 2 (a p e_p)(δ_q c q)
  rw [show (∑ p : Fin n1, ∑ q : Fin n2,
          2 * (a p * (if p = i then (1:ℝ) else 0)) * ((if q = j then (1:ℝ) else 0) * c q))
        = (∑ p : Fin n1, 2 * (a p * (if p = i then (1:ℝ) else 0)))
            * (∑ q : Fin n2, ((if q = j then (1:ℝ) else 0) * c q))
      from by
        rw [← factor (fun p => 2 * (a p * (if p = i then (1:ℝ) else 0)))
              (fun q => (if q = j then (1:ℝ) else 0) * c q)]]
  -- T5 = ∑∑ 2 (a p)^2 (δ_q c q)
  rw [show (∑ p : Fin n1, ∑ q : Fin n2,
          2 * (a p)^2 * ((if q = j then (1:ℝ) else 0) * c q))
        = (∑ p : Fin n1, 2 * (a p)^2)
            * (∑ q : Fin n2, ((if q = j then (1:ℝ) else 0) * c q))
      from by
        rw [← factor (fun p => 2 * (a p)^2)
              (fun q => (if q = j then (1:ℝ) else 0) * c q)]]
  -- T6 = ∑∑ 2 (a p e_p) (c q)^2
  rw [show (∑ p : Fin n1, ∑ q : Fin n2,
          2 * (a p * (if p = i then (1:ℝ) else 0)) * (c q)^2)
        = (∑ p : Fin n1, 2 * (a p * (if p = i then (1:ℝ) else 0)))
            * (∑ q : Fin n2, (c q)^2)
      from by
        rw [← factor (fun p => 2 * (a p * (if p = i then (1:ℝ) else 0)))
              (fun q => (c q)^2)]]
  -- now substitute all single-sum values
  rw [hsumA, hsumC, sumDelta, sumE, sumDeltaC]
  rw [show (∑ p : Fin n1, 2 * (a p * (if p = i then (1:ℝ) else 0)))
        = 2 * a i from by rw [← Finset.mul_sum, sumAE]]
  rw [show (∑ p : Fin n1, 2 * (a p)^2)
        = 2 * rowEnergy S.u i from by rw [← Finset.mul_sum, hsumA]]
  rw [haii, hcjj]
  ring

/-- From coherence ≤ μ₀ we get a per-row energy bound rowEnergy u i ≤ μ₀ r / N. -/
theorem rowEnergy_le_of_coherence {N r : Nat} (u : Fin r → (Fin N → ℝ)) (mu0 : ℝ)
    (hN : 0 < N) (hr : 0 < r) (hcoh : coherence N r u ≤ mu0) (i : Fin N) :
    rowEnergy u i ≤ mu0 * (r : ℝ) / (N : ℝ) := by
  -- rowEnergy u i ≤ ⨆ rowEnergy
  have hbdd : BddAbove (Set.range (fun i : Fin N => ∑ k : Fin r, (u k i)^2)) :=
    Set.Finite.bddAbove (Set.finite_range _)
  have hle : rowEnergy u i ≤ ⨆ i : Fin N, ∑ k : Fin r, (u k i)^2 := by
    rw [rowEnergy]; exact le_ciSup hbdd i
  -- coherence = (N/r) * sup
  unfold coherence at hcoh
  set S := ⨆ i : Fin N, ∑ k : Fin r, (u k i)^2 with hS
  -- hcoh : (N / r) * S ≤ mu0
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  -- multiply hcoh by (r/N) > 0
  have hkey : S ≤ mu0 * (r:ℝ) / (N:ℝ) := by
    have h2 : ((N:ℝ)/r) * S * (r / N) ≤ mu0 * (r / N) := by
      apply mul_le_mul_of_nonneg_right hcoh
      positivity
    have hsimp : ((N:ℝ)/r) * S * (r / N) = S := by
      field_simp
    rw [hsimp] at h2
    calc S ≤ mu0 * (r / N) := h2
      _ = mu0 * (r:ℝ) / (N:ℝ) := by ring
  exact le_trans hle hkey

/-- frobeniusNorm X ^ 2 = frobeniusNormSq X (since frobeniusNormSq ≥ 0). -/
theorem frobeniusNorm_sq_eq {n1 n2 : Nat} (X : RealMatrix n1 n2) :
    frobeniusNorm X ^ 2 = frobeniusNormSq X := by
  unfold frobeniusNorm
  rw [Real.sq_sqrt]
  unfold frobeniusNormSq
  apply Finset.sum_nonneg; intro i _; apply Finset.sum_nonneg; intro j _; positivity

/-- rowEnergy is nonnegative. -/
theorem rowEnergy_nonneg {N r : Nat} (u : Fin r → (Fin N → ℝ)) (i : Fin N) :
    0 ≤ rowEnergy u i := by
  rw [rowEnergy]; apply Finset.sum_nonneg; intro k _; positivity

end MatrixCompletion

open MatrixCompletion

/-- The CORRECTED Candès–Recht coordinate Frobenius bound:
    ‖P_T(e_ij)‖²_F ≤ 2 μ₀ r / min(n₁,n₂). -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (S : SVD M r) (μ₀ : ℝ) :
    0 < n₁ → 0 < n₂ → 0 < r → 1 ≤ μ₀ → A0 S μ₀ →
    TangentCoordinateFrobeniusBound S
      (2 * μ₀ * (r : ℝ) / (min n₁ n₂ : ℝ)) := by
  intro h1 h2 h3 h4 h5 i j
  rw [frobeniusNorm_sq_eq, tangent_coord_frobSq S i j]
  obtain ⟨hcu, hcv⟩ := h5
  set α := rowEnergy S.u i with hα
  set γ := rowEnergy S.v j with hγ
  have hαnn : 0 ≤ α := rowEnergy_nonneg S.u i
  have hγnn : 0 ≤ γ := rowEnergy_nonneg S.v j
  have hαb : α ≤ μ₀ * (r:ℝ) / (n₁:ℝ) := rowEnergy_le_of_coherence S.u μ₀ h1 h3 hcu i
  have hγb : γ ≤ μ₀ * (r:ℝ) / (n₂:ℝ) := rowEnergy_le_of_coherence S.v μ₀ h2 h3 hcv j
  have step1 : α + γ - α * γ ≤ α + γ := by nlinarith [mul_nonneg hαnn hγnn]
  have hμr : 0 ≤ μ₀ * (r:ℝ) := by
    have : (0:ℝ) ≤ μ₀ := le_trans (by norm_num) h4
    positivity
  have hminpos : (0:ℝ) < (min n₁ n₂ : ℝ) := by
    have : 0 < min n₁ n₂ := by omega
    exact_mod_cast this
  have hn1pos : (0:ℝ) < (n₁:ℝ) := by exact_mod_cast h1
  have hn2pos : (0:ℝ) < (n₂:ℝ) := by exact_mod_cast h2
  have hmin1 : (min n₁ n₂ : ℝ) ≤ (n₁:ℝ) := by exact_mod_cast Nat.min_le_left n₁ n₂
  have hmin2 : (min n₁ n₂ : ℝ) ≤ (n₂:ℝ) := by exact_mod_cast Nat.min_le_right n₁ n₂
  have b1 : μ₀ * (r:ℝ) / (n₁:ℝ) ≤ μ₀ * (r:ℝ) / (min n₁ n₂ : ℝ) :=
    div_le_div_of_nonneg_left hμr hminpos hmin1
  have b2 : μ₀ * (r:ℝ) / (n₂:ℝ) ≤ μ₀ * (r:ℝ) / (min n₁ n₂ : ℝ) :=
    div_le_div_of_nonneg_left hμr hminpos hmin2
  have hfinal : α + γ ≤ 2 * μ₀ * (r:ℝ) / (min n₁ n₂ : ℝ) := by
    have heq : μ₀ * (r:ℝ) / (min n₁ n₂ : ℝ) + μ₀ * (r:ℝ) / (min n₁ n₂ : ℝ)
        = 2 * μ₀ * (r:ℝ) / (min n₁ n₂ : ℝ) := by ring
    linarith [hαb, hγb, b1, b2]
  linarith [step1, hfinal]
