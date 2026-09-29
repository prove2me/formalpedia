-- Prove2me | solution 1 for mme_rational_coarse_penalty_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T07:04:39.904154+00:00
-- url     : https://prove2.me/submissions/a3ceb9e5-95b3-470f-9548-41b6eab4a56d

import Theorems.Thm_mme_entropy_dyadic_bounds
import Theorems.Thm_mme_cross_entropy_dyadic_upper
import Theorems.Thm_mme_entropy_penalty_le_pair_reference

open scoped BigOperators
open MME.RegionRate MME.RecursiveThinSplit

/-- A rational arithmetic certificate proves a lower bound for the coarse
entropy minus its maximum-entropy penalty. The certificate includes the
reference probabilities, dyadic exponents and all finite marginal sums. -/
theorem solution
    {half : ℕ} {parent : Fin 3 → ℕ} (alpha : Split half parent → ℚ)
    (ha : ∀ c, 0 ≤ alpha c) (hprob : ∑ c, alpha c = 1)
    (i j : Fin 3) (hij : i ≠ j) (p q : Fin (half + 1) → ℚ)
    (hp : ∀ v, 0 < p v) (hq : ∀ v, 0 < q v)
    (hpmass : ∑ v, p v = 1) (hqmass : ∑ v, q v = 1)
    (k0 kp kq : Fin (half + 1) → ℕ) (ka : Split half parent → ℕ) (b : ℚ) :
    let m := fun i v => ∑ c : {c : Split half parent // c.val i = v}, alpha c.val
    b ≤
      (∑ v, m 0 v * ((k0 v : ℚ) * (693147180 / 1000000000) + 1 -
        2 ^ k0 v * m 0 v)) +
      (∑ c, alpha c * ((ka c : ℚ) * (693147180 / 1000000000) + 1 -
        2 ^ ka c * alpha c)) -
      (∑ v, m i v * ((kp v : ℚ) * (693147181 / 1000000000) - 1 +
        (2 ^ kp v * p v)⁻¹)) -
      (∑ v, m j v * ((kq v : ℚ) * (693147181 / 1000000000) - 1 +
        (2 ^ kq v * q v)⁻¹)) →
    (b : ℝ) ≤
      entropy (mme_modern_marginal (fun c : Split half parent => c.val 0)
        (fun c => (alpha c : ℝ))) -
      Real.log 2 * entropyPenalty (fun c => (alpha c : ℝ)) := by
  dsimp only
  intro hcert
  let m := fun i v => ∑ c : {c : Split half parent // c.val i = v}, alpha c.val
  have hmcast (i : Fin 3) (v : Fin (half + 1)) :
      (m i v : ℝ) = mme_modern_marginal (fun c : Split half parent => c.val i)
        (fun c => (alpha c : ℝ)) v := by
    simp [m, mme_modern_marginal]
  have haR (c : Split half parent) : (0 : ℝ) ≤ alpha c := by exact_mod_cast ha c
  have hmR (i : Fin 3) (v : Fin (half + 1)) : (0 : ℝ) ≤ m i v := by
    have hmQ : 0 ≤ m i v :=
      Finset.sum_nonneg (fun (c : {c : Split half parent // c.val i = v}) _ => ha c.val)
    exact_mod_cast hmQ
  have hprobR : ∑ c, (alpha c : ℝ) = 1 := by exact_mod_cast hprob
  have hpR (v : Fin (half + 1)) : (0 : ℝ) < p v := by exact_mod_cast hp v
  have hqR (v : Fin (half + 1)) : (0 : ℝ) < q v := by exact_mod_cast hq v
  have hpmassR : ∑ v, (p v : ℝ) = 1 := by exact_mod_cast hpmass
  have hqmassR : ∑ v, (q v : ℝ) = 1 := by exact_mod_cast hqmass
  have hcoarse := (mme_entropy_dyadic_bounds (fun v => (m 0 v : ℝ)) (hmR 0) k0).1
  have hjoint := (mme_entropy_dyadic_bounds (fun c => (alpha c : ℝ)) haR ka).1
  have hcrossp := mme_cross_entropy_dyadic_upper (fun v => (m i v : ℝ))
    (fun v => (p v : ℝ)) (hmR i) hpR kp
  have hcrossq := mme_cross_entropy_dyadic_upper (fun v => (m j v : ℝ))
    (fun v => (q v : ℝ)) (hmR j) hqR kq
  have hpen := mme_entropy_penalty_le_pair_reference (fun c => (alpha c : ℝ))
    haR hprobR i j hij (fun v => (p v : ℝ)) (fun v => (q v : ℝ))
    hpR hqR hpmassR hqmassR
  change b ≤
    (∑ v, m 0 v * ((k0 v : ℚ) * (693147180 / 1000000000) + 1 -
      2 ^ k0 v * m 0 v)) +
    (∑ c, alpha c * ((ka c : ℚ) * (693147180 / 1000000000) + 1 -
      2 ^ ka c * alpha c)) -
    (∑ v, m i v * ((kp v : ℚ) * (693147181 / 1000000000) - 1 +
      (2 ^ kp v * p v)⁻¹)) -
    (∑ v, m j v * ((kq v : ℚ) * (693147181 / 1000000000) - 1 +
      (2 ^ kq v * q v)⁻¹)) at hcert
  have hcertR := (Rat.cast_le (K := ℝ)).2 hcert
  push_cast at hcertR
  simp_rw [← hmcast] at hpen
  have hmfun : mme_modern_marginal (fun c : Split half parent => c.val 0)
      (fun c => (alpha c : ℝ)) = fun v => (m 0 v : ℝ) :=
    funext (fun v => (hmcast 0 v).symm)
  rw [hmfun]
  linarith


#print axioms solution
