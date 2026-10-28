-- Prove2me | Theorems.Thm_gpy_secondMoment_bvErrBound
-- name    : gpy_secondMoment_bvErrBound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-27T20:50:10.922135+00:00
-- url     : https://prove2.me/theorems/481846d8-fac2-49ab-b2b8-a7b676820fca
-- title:
--   Second-moment BV error control for GPY tuple weights, with λ-mass and level bounds
-- statement:
--   Let h be a tuple of shifts, R a level, and λ coefficients supported on tuples d with 1 ≤ dᵢ ≤ R and ∏ᵢ dᵢ ≤ R. Let w(n) be the GPY weight (∑_{d: dᵢ ∣ n+hᵢ} λ_d)², let S₂ = ∑_{x<n≤y} (∑ᵢ 1_prime(n+hᵢ)) w(n) be the second moment, and let Λ = ∑_{d,e} |λ_d λ_e| be the total λ-mass. Let M be any model function and E any nonnegative error bound such that every coprime-residue model error at modulus at most R² is bounded by E. Then for x ≤ y, S₂ differs from the main-term sum (λ_d λ_e times the model differences M(y+hᵢ) − M(x+hᵢ), summed over good support pairs) by at most Λ · (R² · ∑ᵢ (E(y+hᵢ) + E(x+hᵢ)) + k). The coprime restriction is essential: the good-pair witness residue is itself coprime, and non-coprime residues are not controlled by Bombieri–Vinogradov. The level bound L ≤ R² for support pairs puts every combined modulus inside the BV range when R² < Y^(1/2−η).
-- source:
--   GPY second-moment BV error control (λ-mass bound with level R², under a BV-max input hypothesis), formalized from the GPY tuple weight setup, the general CRT count, the first-moment main term, the second-moment interchange, and the second-moment BV evaluation

import Mathlib
open Classical

theorem gpy_secondMoment_bvErrBound (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) (E : ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (hE : ∀ Y, 0 ≤ E Y)
    (hErr : ∀ Y L r, L ≤ R ^ 2 → Nat.Coprime r L →
      abs (((((Finset.range (Y + 1)).filter
        (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)) - M Y L) ≤ E Y) :
    abs (∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2
      - ∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        lam d * lam e *
          (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            then M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
              - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            else 0))
    ≤ (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        abs (lam d * lam e))
      * ((R : ℝ) ^ 2 * (∑ i, (E (y + h i) + E (x + h i))) + k) := by sorry
