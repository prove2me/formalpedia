-- Prove2me | Theorems.Thm_gpy_secondMoment_bvInst
-- name    : gpy_secondMoment_bvInst
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T02:20:42.230577+00:00
-- url     : https://prove2.me/theorems/a766f0d2-a1f3-47a4-935e-222d29261671
-- title:
--   BV instantiation for the GPY second moment: error bound under Bombieri–Vinogradov-style sum bounds
-- statement:
--   Let h be a tuple of shifts, R a level, and λ coefficients supported on tuples d with 1 ≤ dᵢ ≤ R and ∏ᵢ dᵢ ≤ R. Let S₂ be the GPY second moment and let Λ = ∑_{d,e} |λ_d λ_e| be the total λ-mass. Assume BV-style sum bounds at every controlled height (for every coprime choice function, the summed coprime-residue model errors over the BV range are at most C·Y·log(Y)^{−A'}), C ≥ 0, and the level constraint R² < Y^{1/2−η} with 2 ≤ Y' at every interval endpoint y + hᵢ, x + hᵢ. Then for x ≤ y, S₂ differs from the main-term sum for the model li/φ (λ_d λ_e times the model differences li(y+hᵢ)/φ(L) − li(x+hᵢ)/φ(L), summed over good support pairs) by at most Λ · (R² · ∑ᵢ (C·(y+hᵢ)·log(y+hᵢ)^{−A'} + C·(x+hᵢ)·log(x+hᵢ)^{−A'}) + k). The bound is conditional on the BV-style sum bounds, which are hypotheses, not proved here; the level bound L ≤ R² for support pairs puts every combined modulus inside the BV range.
-- source:
--   GPY second-moment BV instantiation (error bound under BV-style sum bounds, conditional form), formalized from the GPY tuple weight setup, the general CRT count, the first-moment main term, the second-moment interchange, the second-moment BV evaluation, and the second-moment BV error control

import Mathlib
open Classical

theorem gpy_secondMoment_bvInst {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) {x y : ℕ} (hxy : x ≤ y)
    {η A' C : ℝ} (hC : 0 ≤ C) (li : ℝ → ℝ)
    (hBV : ∀ Y' : ℕ, 2 ≤ Y' → (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η) →
      ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs (((((Finset.range (Y' + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ v q [MOD q])).card : ℝ)) - li (Y' : ℝ) / (Nat.totient q : ℝ))
          ≤ C * ((Y' : ℝ) * Real.log (Y' : ℝ) ^ (-A')))
    (hlevel : ∀ i, (R : ℝ) ^ 2 < ((y + h i : ℕ) : ℝ) ^ (1 / 2 - η) ∧
      (R : ℝ) ^ 2 < ((x + h i : ℕ) : ℝ) ^ (1 / 2 - η))
    (hY2 : ∀ i, 2 ≤ y + h i ∧ 2 ≤ x + h i) :
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
            then li ((y + h i : ℕ) : ℝ) / (Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ)
              - li ((x + h i : ℕ) : ℝ) / (Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ)
            else 0))
    ≤ (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        abs (lam d * lam e))
      * ((R : ℝ) ^ 2 * (∑ i, (C * (((y + h i : ℕ) : ℝ) * Real.log ((y + h i : ℕ) : ℝ) ^ (-A'))
          + C * (((x + h i : ℕ) : ℝ) * Real.log ((x + h i : ℕ) : ℝ) ^ (-A')))) + (k : ℝ)) := by sorry
