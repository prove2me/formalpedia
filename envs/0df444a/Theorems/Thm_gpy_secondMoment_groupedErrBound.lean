-- Prove2me | Theorems.Thm_gpy_secondMoment_groupedErrBound
-- name    : gpy_secondMoment_groupedErrBound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T17:34:13.377116+00:00
-- url     : https://prove2.me/theorems/ebdbd6ba-7da6-4bb9-bfe5-c197345e31e9
-- title:
--   GPY second moment: error bound grouped by modulus with fiber weights
-- statement:
--   Let h be a tuple of shifts, R a level, and λ coefficients supported on tuples d with 1 ≤ dᵢ ≤ R and ∏ᵢ dᵢ ≤ R. Let S₂ be the GPY second moment and let the BV main term be as in the tight bound. Group the good-pair witness errors by their combined modulus L = lcm of the coordinatewise lcms, with fiber weight equal to the total |λ_d λ_e| over support pairs with combined modulus L that are good at the coordinate, and let the max coprime-residue model error at a height and modulus be the finite maximum of the model errors over coprime residues. Then for x ≤ y, S₂ differs from the BV main term by at most the sum over coordinates and over L ≤ R² of the fiber weight times the sum of the max errors at the two endpoints, plus Λ·k where Λ is the total λ-mass ∑_{d,e} |λ_d λ_e| and k is the tuple length. The modulus range is R²+1 because every support pair has combined modulus at most R².
-- source:
--   GPY second-moment error bound grouped by modulus with fiber weights, formalized from the GPY tuple weight setup, the general CRT count, the first-moment main term, the second-moment interchange, the second-moment BV evaluation, and the tight single-residue error bound

import Mathlib
open Classical

theorem gpy_secondMoment_groupedErrBound (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) :
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
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
            M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
              - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))
            else 0))
      ≤ (∑ i, ∑ L ∈ Finset.range (R ^ 2 + 1),
          (∑ p ∈ ((Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R) ×ˢ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R)).filter
              (fun p => (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
            abs (lam p.1 * lam p.2)) * ((if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
              (fun r => abs ((((Finset.range (y + h i + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M (y + h i) L))).Nonempty then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
              (fun r => abs ((((Finset.range (y + h i + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M (y + h i) L))).max' hne else 0) + (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
              (fun r => abs ((((Finset.range (x + h i + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M (x + h i) L))).Nonempty then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
              (fun r => abs ((((Finset.range (x + h i + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ) - M (x + h i) L))).max' hne else 0)))
        + (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), abs (lam d * lam e)) * (k : ℝ) := by sorry
