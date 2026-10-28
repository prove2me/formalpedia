-- Prove2me | Theorems.Thm_gpy_secondMoment_weightedBV_bound
-- name    : gpy_secondMoment_weightedBV_bound
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T17:37:37.094988+00:00
-- url     : https://prove2.me/theorems/2380dab9-76dd-45d1-ae03-1673c836dcad
-- title:
--   GPY second moment: weighted BV error bound
-- statement:
--   Let h be a tuple of shifts, R a level, and λ coefficients supported on tuples d with 1 ≤ dᵢ ≤ R and ∏ᵢ dᵢ ≤ R. Let S₂ be the GPY second moment and let the BV main term be as in the tight bound. Assume platform-shaped BV sum bounds at every endpoint height (for every coprime choice function, the summed model errors over the BV range are at most B(Y')), the level constraint R² < Y'^{1/2−η} with 2 ≤ Y' at every interval endpoint y + hᵢ, x + hᵢ, and a uniform fiber bound: every fiber weight is at most Wbar ≥ 0. Then for x ≤ y, S₂ differs from the BV main term by at most Wbar times the sum over coordinates of B(y + hᵢ) + B(x + hᵢ), plus Λ·k where Λ is the total λ-mass and k the tuple length. The bound is conditional on the BV-style sum bounds, which are hypotheses, not proved here; the content is that the errors stay inside a sum over moduli weighted by the fibers instead of collapsing each one to the whole BV sum.
-- source:
--   GPY second-moment weighted BV error bound (conditional corollary under platform-shaped BV sum bounds plus a uniform fiber bound), formalized from the GPY tuple weight setup, the general CRT count, the first-moment main term, the second-moment interchange, the second-moment BV evaluation, the tight single-residue error bound, and the grouped error bound

import Mathlib
open Classical

theorem gpy_secondMoment_weightedBV_bound (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (M : ℕ → ℕ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    {η : ℝ} (B : ℕ → ℝ)
    (hBV : ∀ Y' : ℕ, 2 ≤ Y' → (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η) →
      ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs ((((Finset.range (Y' + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ v q [MOD q])).card : ℝ) - M Y' q) ≤ B Y')
    (hlevel : ∀ i, (R : ℝ) ^ 2 < ((y + h i : ℕ) : ℝ) ^ (1 / 2 - η) ∧
      (R : ℝ) ^ 2 < ((x + h i : ℕ) : ℝ) ^ (1 / 2 - η))
    (hY2 : ∀ i, 2 ≤ y + h i ∧ 2 ≤ x + h i)
    (Wbar : ℝ) (hWnn : 0 ≤ Wbar)
    (hW : ∀ i L, (∑ p ∈ ((Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R) ×ˢ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R)).filter
              (fun p => (∃ w, (∀ j, Nat.lcm (p.1 j) (p.2 j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)))) ∧ Finset.lcm Finset.univ (fun j => Nat.lcm (p.1 j) (p.2 j)) = L),
            abs (lam p.1 * lam p.2)) ≤ Wbar) :
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
      ≤ Wbar * (∑ i, (B (y + h i) + B (x + h i)))
        + (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R), abs (lam d * lam e)) * (k : ℝ) := by sorry
