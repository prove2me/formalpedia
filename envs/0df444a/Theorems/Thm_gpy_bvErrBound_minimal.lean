-- Prove2me | Theorems.Thm_gpy_bvErrBound_minimal
-- name    : gpy_bvErrBound_minimal
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T21:47:54.314673+00:00
-- url     : https://prove2.me/theorems/fc232b09-ce56-4546-a274-893231b5b7d6
-- title:
--   Minimal weights: instantiated BV error bound
-- statement:
--   Let h be a tuple of shifts, R ≥ 2 a level, kk an exponent, M any model function, and E any nonnegative error bound such that every coprime-residue model error at modulus at most R² is bounded by E. For x ≤ y, the GPY second moment S₂ for the minimal tuple weights λ_d = (∏ᵢ μ(dᵢ)) · (1 − log(∏ᵢ dᵢ)/log R)^kk, truncated to zero when ∏ᵢ dᵢ > R, differs from its BV main term (λ_d λ_e times the model differences M(y+hᵢ) − M(x+hᵢ), summed over good support pairs) by at most R^(2k) · (R² · ∑ᵢ (E(y+hᵢ) + E(x+hᵢ)) + k), using the crude mass bound Λ ≤ R^(2k). Honest scope note: this does NOT close the GPY argument for any kk — the error term is of order R^(2k+2) · Y · log^(−A′) once E ~ Y · log^(−A′) is plugged in, against a main term at most of order R^(2k) · Y. It is a foundation error-bound result, not a separation claim.
-- source:
--   GPY minimal polynomial-truncated lambda weights: second-moment BV error bound with the crude mass bound substituted

import Mathlib
open Classical

theorem gpy_bvErrBound_minimal {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (kk : ℕ) (M : ℕ → ℕ → ℝ) (E : ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y) (hR : 2 ≤ R)
    (hE : ∀ Y, 0 ≤ E Y)
    (hErr : ∀ Y L r, L ≤ R ^ 2 → Nat.Coprime r L →
      abs (((((Finset.range (Y + 1)).filter
        (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y L) ≤ E Y) :
    abs (∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then
            ((∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℝ)) *
              (if ∏ i, d i ≤ R then
                (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log (R : ℝ)) ^ kk
              else 0)) else 0) ^ 2
      - ∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ((∏ i, ((ArithmeticFunction.moebius (d i) : ℤ) : ℝ)) *
            (if ∏ i, d i ≤ R then
              (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log (R : ℝ)) ^ kk
            else 0))
        * ((∏ i, ((ArithmeticFunction.moebius (e i) : ℤ) : ℝ)) *
            (if ∏ i, e i ≤ R then
              (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log (R : ℝ)) ^ kk
            else 0))
        * (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            then M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
              - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            else 0))
      ≤ (R : ℝ) ^ (2 * k) *
        ((R : ℝ) ^ 2 * (∑ i, (E (y + h i) + E (x + h i))) + k) := by sorry
