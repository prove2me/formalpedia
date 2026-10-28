-- Prove2me | Theorems.Thm_gpy_secondMoment_bvMainTerm
-- name    : gpy_secondMoment_bvMainTerm
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-27T19:18:09.589457+00:00
-- url     : https://prove2.me/theorems/ede4c005-a6b5-4884-bf4c-e9034335f85d
-- title:
--   Second-moment BV evaluation for GPY tuple weights: main term + BV error term
-- statement:
--   Let h be a tuple of shifts, R a level, and λ coefficients supported on tuples d with 1 ≤ dᵢ ≤ R and ∏ᵢ dᵢ ≤ R. Let w(n) be the GPY weight (∑_{d: dᵢ ∣ n+hᵢ} λ_d)² and let S₂ = ∑_{x<n≤y} (∑ᵢ 1_prime(n+hᵢ)) w(n) be the second moment. For any model function M and any x ≤ y, S₂ differs from the main-term sum — λ_d λ_e times the model differences M(y+hᵢ) − M(x+hᵢ), summed over good support pairs — by at most the error bound: the λ-mass times the model-error sums over good pairs, plus 1 per bad pair. A pair is good when some witness has (w+hᵢ, L) = 1 for the combined modulus L; otherwise its prime count is at most 1. Incompatible pairs contribute exactly 0 to both sides.
-- source:
--   GPY second-moment BV evaluation (main term + BV error term, for an abstract model M), formalized from the GPY tuple weight setup, the general CRT count, the first-moment main term, and the second-moment interchange

import Mathlib
open Classical

theorem gpy_secondMoment_bvMainTerm (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y) :
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
    ≤ ∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        abs (lam d * lam e) *
          (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            then (∑ r ∈ Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))),
                  abs ((((Finset.range (y + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))])).card : ℝ)
                    - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
              + (∑ r ∈ Finset.range (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))),
                  abs ((((Finset.range (x + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))])).card : ℝ)
                    - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
            else 1) := by sorry
