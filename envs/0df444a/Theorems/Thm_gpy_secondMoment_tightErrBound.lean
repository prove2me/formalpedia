-- Prove2me | Theorems.Thm_gpy_secondMoment_tightErrBound
-- name    : gpy_secondMoment_tightErrBound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T17:31:42.991529+00:00
-- url     : https://prove2.me/theorems/4dcef77f-a74a-4479-958e-fadd2af0ebaa
-- title:
--   GPY second moment: tight single-residue error bound
-- statement:
--   Let h be a tuple of shifts, R a level, and λ coefficients supported on tuples d with 1 ≤ dᵢ ≤ R and ∏ᵢ dᵢ ≤ R. Let S₂ be the GPY second moment and let the BV main term be the sum over support pairs of λ_d λ_e times the model differences at the interval endpoints for good pairs (0 for bad pairs). Then for x ≤ y, and for any witness selector wit satisfying the divisibility and coprimality conditions at good pairs, S₂ differs from the BV main term by at most the sum over support pairs of |λ_d λ_e| times the sum over coordinates of the two witness errors at the endpoints (1 for bad pairs). The bound uses the two witness errors directly: there is no sum over coprime residues, no cardinality factor, and no R² factor anywhere.
-- source:
--   GPY second-moment tight single-residue error bound (per-triple witness errors via jointPrimeCount_approx), formalized from the GPY tuple weight setup, the general CRT count, the first-moment main term, the second-moment interchange, and the second-moment BV evaluation

import Mathlib
open Classical

theorem gpy_secondMoment_tightErrBound (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
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
      ≤ ∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        abs (lam d * lam e) * (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then
              abs ((((Finset.range (y + h i + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ wit d e i + h i [MOD Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))])).card : ℝ)
                - M (y + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
              + abs ((((Finset.range (x + h i + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ wit d e i + h i [MOD Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))])).card : ℝ)
                - M (x + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            else 1) := by sorry
