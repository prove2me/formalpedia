-- Prove2me | solution 1 for LinearOptimization.interior_point_potential_reduction
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-08-06T21:21:40.301098+00:00
-- url     : https://prove2.me/submissions/6e4a1d9d-7c78-4aa0-85a7-f317269b292a

import Definitions.Def_LinearOptimization_InteriorPointPotential

/-!
# Theorem 9.4 (Bertsimas & Tsitsiklis, p. 411)

If the primal-dual potential drops by at least `δ` per iteration, the duality
gap falls below `ε` within `K = ⌈(G⁰ + (q−n)log(1/ε) − n log n)/δ⌉` iterations.

The only analytic ingredient is the arithmetic-geometric bound
`∑ⱼ log(xⱼsⱼ) ≤ n log(s'x / n)` (from `log t ≤ t − 1` applied to
`tⱼ = n xⱼsⱼ / s'x`), which gives `G(x,s) ≥ (q−n) log s'x + n log n`.
-/

open Matrix

namespace Potential

open LinearOptimization

variable {n : ℕ}

/-- `G(x,s) ≥ (q−n) log(s'x) + n log n` for positive `x`, `s`. -/
lemma potential_lower (hn : 0 < n) (q : ℝ) (x s : Fin n → ℝ)
    (hx : ∀ j, 0 < x j) (hs : ∀ j, 0 < s j) :
    (q - (n : ℝ)) * Real.log (s ⬝ᵥ x) + (n : ℝ) * Real.log (n : ℝ)
      ≤ interiorPointPotential q x s := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hTpos : 0 < s ⬝ᵥ x := by
    simp only [dotProduct]
    refine Finset.sum_pos (fun j _ => mul_pos (hs j) (hx j)) ?_
    exact Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
  set T : ℝ := s ⬝ᵥ x with hT
  have hTne : T ≠ 0 := ne_of_gt hTpos
  -- the normalized products sum to `n`
  have hsum : ∑ j, (n : ℝ) * (x j * s j) / T = (n : ℝ) := by
    have h1 : ∀ j, (n : ℝ) * (x j * s j) / T = ((n : ℝ) / T) * (x j * s j) := fun j => by ring
    rw [Finset.sum_congr rfl (fun j _ => h1 j), ← Finset.mul_sum]
    have h2 : ∑ j, x j * s j = T := by
      rw [hT]; simp only [dotProduct]
      exact Finset.sum_congr rfl (fun j _ => mul_comm _ _)
    rw [h2]
    field_simp
  have hupos : ∀ j, 0 < (n : ℝ) * (x j * s j) / T :=
    fun j => div_pos (mul_pos hnR (mul_pos (hx j) (hs j))) hTpos
  -- `∑ log uⱼ ≤ 0`
  have hlogu : ∑ j, Real.log ((n : ℝ) * (x j * s j) / T) ≤ 0 := by
    have h1 : ∑ j, Real.log ((n : ℝ) * (x j * s j) / T)
        ≤ ∑ j, ((n : ℝ) * (x j * s j) / T - 1) :=
      Finset.sum_le_sum (fun j _ => Real.log_le_sub_one_of_pos (hupos j))
    have h2 : ∑ j, ((n : ℝ) * (x j * s j) / T - 1) = 0 := by
      rw [Finset.sum_sub_distrib, hsum]
      simp
    linarith
  -- the AM-GM bound
  have hkey : ∑ j, Real.log (x j) + ∑ j, Real.log (s j)
      ≤ (n : ℝ) * Real.log (T / (n : ℝ)) := by
    have hsplit : ∑ j, Real.log (x j) + ∑ j, Real.log (s j)
        = ∑ j, Real.log (x j * s j) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun j _ =>
        (Real.log_mul (ne_of_gt (hx j)) (ne_of_gt (hs j))).symm)
    have hfac : ∀ j, Real.log (x j * s j)
        = Real.log (T / (n : ℝ)) + Real.log ((n : ℝ) * (x j * s j) / T) := by
      intro j
      rw [← Real.log_mul (by positivity) (ne_of_gt (hupos j))]
      congr 1
      field_simp
    rw [hsplit, Finset.sum_congr rfl (fun j _ => hfac j), Finset.sum_add_distrib,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    linarith
  have hlogdiv : Real.log (T / (n : ℝ)) = Real.log T - Real.log (n : ℝ) :=
    Real.log_div hTne (ne_of_gt hnR)
  simp only [interiorPointPotential, ← hT]
  rw [hlogdiv] at hkey
  nlinarith [hkey]

end Potential

open LinearOptimization Potential
open Matrix

theorem solution {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) (c : Fin n → ℝ)
    (q delta eps : ℝ) (hq : (n : ℝ) < q) (hdelta : 0 < delta)
    (heps : 0 < eps)
    (x : ℕ → Fin n → ℝ) (p : ℕ → Fin m → ℝ) (s : ℕ → Fin n → ℝ)
    (hfeas : ∀ k, A.mulVec (x k) = b ∧ (∀ j, 0 < x k j) ∧
      Aᵀ.mulVec (p k) + s k = c ∧ (∀ j, 0 < s k j))
    (hdec : ∀ k, interiorPointPotential q (x (k + 1)) (s (k + 1)) ≤
      interiorPointPotential q (x k) (s k) - delta)
    (K : ℕ)
    (hK : K = ⌈(interiorPointPotential q (x 0) (s 0) +
      (q - n) * Real.log (1 / eps) - n * Real.log n) / delta⌉₊) :
    s K ⬝ᵥ x K ≤ eps := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- with no variables the gap is `0`
    subst hn
    simp only [dotProduct]
    simpa using heps.le
  -- the potential drops linearly
  have hstep : ∀ k : ℕ, interiorPointPotential q (x k) (s k)
      ≤ interiorPointPotential q (x 0) (s 0) - (k : ℝ) * delta := by
    intro k
    induction k with
    | zero => simp
    | succ j ih =>
        have := hdec j
        push_cast
        linarith
  have hlow := potential_lower hn q (x K) (s K) (hfeas K).2.1 (hfeas K).2.2.2
  have hceil : (interiorPointPotential q (x 0) (s 0) +
      (q - n) * Real.log (1 / eps) - n * Real.log n) / delta ≤ (K : ℝ) := by
    rw [hK]; exact Nat.le_ceil _
  have hKdelta : interiorPointPotential q (x 0) (s 0) +
      (q - n) * Real.log (1 / eps) - n * Real.log n ≤ (K : ℝ) * delta := by
    rw [div_le_iff₀ hdelta] at hceil
    exact hceil
  have hTpos : 0 < s K ⬝ᵥ x K := by
    simp only [dotProduct]
    refine Finset.sum_pos (fun j _ => mul_pos ((hfeas K).2.2.2 j) ((hfeas K).2.1 j)) ?_
    exact Finset.univ_nonempty_iff.2 (Fin.pos_iff_nonempty.1 hn)
  have hloginv : Real.log (1 / eps) = -Real.log eps := by
    rw [one_div, Real.log_inv]
  have hqn : 0 < q - (n : ℝ) := by linarith
  have hlog : Real.log (s K ⬝ᵥ x K) ≤ Real.log eps := by
    have h1 := hstep K
    have h2 : (q - (n : ℝ)) * Real.log (s K ⬝ᵥ x K)
        ≤ (q - (n : ℝ)) * Real.log eps := by
      rw [hloginv] at hKdelta
      nlinarith [hlow, h1, hKdelta]
    exact le_of_mul_le_mul_left h2 hqn
  exact (Real.log_le_log_iff hTpos heps).1 hlog
