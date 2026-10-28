-- Prove2me | Theorems.Thm_gpy_bvMainTerm_li_div_totient
-- name    : gpy_bvMainTerm_li_div_totient
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T19:04:08.587983+00:00
-- url     : https://prove2.me/theorems/79f2a3d2-e229-4631-9e33-fea3588db8ca
-- title:
--   Selberg main term as li-differences times singular sum
-- statement:
--   Let h be a tuple of shifts, R a level, lam a tuple weight, and li a real function. For the model M(Y, L) = li(Y)/phi(L), the BV main term (the sum over support pairs (d, e) of lam_d * lam_e times the model difference at the interval endpoints over good pairs) equals the sum over coordinates i of (li(y + h_i) - li(x + h_i)) times the singular sum at i (the sum over good support pairs of lam_d * lam_e / phi(L), where L is the combined modulus). The li-differences do not depend on (d, e), so they factor out of the pair sums.
-- source:
--   GPY Selberg weights: the singular-series reduction of the BV main term for the model li/phi

import Mathlib
open Classical

theorem gpy_bvMainTerm_li_div_totient {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (li : ℝ → ℝ) {x y : ℕ} :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        lam d * lam e * (∑ i,
          if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i)
                (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            then li ((y + h i : ℕ) : ℝ)
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
              - li ((x + h i : ℕ) : ℝ)
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
            else 0))
      = ∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ))
        * (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
              (fun d => ∏ i, d i ≤ R),
            ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
              (fun d => ∏ i, d i ≤ R),
            if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
              then lam d * lam e
                / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
              else 0) := by sorry
