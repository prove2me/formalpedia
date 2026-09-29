-- Prove2me | solution 1 for mme_boundary_scaled_volume_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T01:17:08.021149+00:00
-- url     : https://prove2.me/submissions/11bd7813-3e40-4ef9-99e3-f0b0dc239de8

import Theorems.Thm_mme_dwz_multinomial_entropy_polynomial_lower
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Definitions.Def_mme_recursive_yz_boundary_data

open scoped BigOperators
open Filter MME.CompleteSplit MME.RecursiveYZ.Boundary
set_option autoImplicit false

private theorem scaled_boundary_log_lower {ell L : ℕ}
    (B : Profile ell L) (hL : 0 < L) (k : ℕ) (hk : 0 < k)
    (C : Profile ell (L * k)) (hcount : ∀ s, C.count s = B.count s * k) :
    (k : ℝ) * ((L : ℝ) * Real.log 2 *
        mme_modern_entropyBits (fun s ↦ (B.count s : ℝ) / (L : ℝ)) +
      ((∑ s, B.count s * ones s : ℕ) : ℝ) * Real.log 5) -
      (Fintype.card (CompleteWord ell) : ℝ) *
        Real.log (6 * ((L * k + 1 : ℕ) : ℝ)) ≤ Real.log (C.dim : ℝ) := by
  classical
  have hm : 0 < ∑ s, B.count s := by rw [B.total]; exact hL
  have h := mme_dwz_multinomial_entropy_polynomial_lower B.count k hk hm
  have hc : (fun s ↦ B.count s * k) = C.count := by funext s; exact (hcount s).symm
  rw [B.total, hc] at h
  have hmulti : (0 : ℝ) < Nat.multinomial Finset.univ C.count := by
    exact_mod_cast Nat.multinomial_pos Finset.univ C.count
  have hp : (0 : ℝ) < 6 * ((L * k + 1 : ℕ) : ℝ) := by positivity
  have hl := Real.log_le_log (Real.exp_pos _) h
  rw [Real.log_exp, Real.log_mul (ne_of_gt (pow_pos hp _)) (ne_of_gt hmulti),
    Real.log_pow] at hl
  have hone : ∑ s, C.count s * ones s = (∑ s, B.count s * ones s) * k := by
    simp only [hcount, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hd : (C.dim : ℝ) =
      (Nat.multinomial Finset.univ C.count : ℝ) *
        (5 : ℝ) ^ (∑ s, C.count s * ones s) := by
    simp only [Profile.dim, Nat.multinomial, C.total, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_ofNat]
  rw [hd, Real.log_mul (ne_of_gt hmulti) (by positivity), Real.log_pow, hone]
  push_cast at hl ⊢
  nlinarith only [hl]

/-- Replication of a boundary histogram attains its entropy and CW-letter rate;
the threshold is uniform over all boundary profiles with that histogram. -/
theorem solution {ell L : ℕ}
    (B : Profile ell L) (hL : 0 < L) (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ C : Profile ell (L * k),
      (∀ s, C.count s = B.count s * k) →
      (k : ℝ) * ((L : ℝ) * Real.log 2 *
          mme_modern_entropyBits (fun s ↦ (B.count s : ℝ) / (L : ℝ)) +
        ((∑ s, B.count s * ones s : ℕ) : ℝ) * Real.log 5 - delta) ≤
          Real.log (C.dim : ℝ) := by
  classical
  let a : ℝ := Fintype.card (CompleteWord ell)
  have ha : 0 ≤ a := by positivity
  have habs := mme_log_sqrt_loss_eventually_le_linear a 0
    (a * Real.log (6 * ((L : ℝ) + 1))) delta hdelta
  filter_upwards [habs, eventually_gt_atTop 0] with k hk hkpos
  intro C hcount
  have hlog := scaled_boundary_log_lower B hL k hkpos C hcount
  have hpoly : (6 : ℝ) * ((L * k + 1 : ℕ) : ℝ) ≤
      (6 * ((L : ℝ) + 1)) * ((k : ℝ) + 1) := by
    push_cast
    nlinarith [show (0 : ℝ) ≤ L from Nat.cast_nonneg L,
      show (0 : ℝ) ≤ k from Nat.cast_nonneg k]
  have hlogs := Real.log_le_log (by positivity : (0 : ℝ) <
    6 * ((L * k + 1 : ℕ) : ℝ)) hpoly
  rw [Real.log_mul (show (6 * ((L : ℝ) + 1)) ≠ 0 by positivity)
    (show ((k : ℝ) + 1) ≠ 0 by positivity)] at hlogs
  have hscaled := mul_le_mul_of_nonneg_left hlogs ha
  change a * Real.log ((k : ℝ) + 1) + 0 * Real.sqrt ((k : ℝ) + 1) +
    a * Real.log (6 * ((L : ℝ) + 1)) ≤ (k : ℝ) * delta at hk
  change (k : ℝ) * _ - a * _ ≤ _ at hlog
  nlinarith only [hlog, hscaled, hk]


#print axioms solution
