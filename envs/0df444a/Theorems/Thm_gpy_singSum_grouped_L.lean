-- Prove2me | Theorems.Thm_gpy_singSum_grouped_L
-- name    : gpy_singSum_grouped_L
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T19:04:09.057638+00:00
-- url     : https://prove2.me/theorems/68572fb5-31f4-417f-b8c3-e5126d0826b9
-- title:
--   Selberg singular sum grouped by modulus
-- statement:
--   Let h be a tuple of shifts, R a level, lam a tuple weight, and i a coordinate. The singular sum at i (the sum over good support pairs (d, e) of lam_d * lam_e / phi(L), where L is the combined modulus and a pair is good at i when some witness w of the joint divisibility system has w + h_i coprime to L) equals the sum over moduli L in [1, R^2] of (1/phi(L)) times the pair sum at exact modulus L (the sum over support pairs with combined modulus exactly L that are good at i of lam_d * lam_e). The level bound L <= R^2 for support pairs keeps the modulus range finite. This is a different grouping from the monomial grouped form: here the pair sum is not expanded in monomials.
-- source:
--   GPY Selberg weights: the singular sum grouped by combined modulus, from the tuple support and the level bound L <= R^2 for support pairs

import Mathlib
open Classical

theorem gpy_singSum_grouped_L {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (i : Fin k) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i)
              (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
          then lam d * lam e
            / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
          else 0)
      = ∑ L ∈ Finset.Icc 1 (R ^ 2),
        (1 / ((Nat.totient L : ℕ) : ℝ)) *
          (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
              (fun d => ∏ i, d i ≤ R),
            ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
              (fun d => ∏ i, d i ≤ R),
            if (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) = L
              ∧ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))))
            then lam d * lam e else 0) := by sorry
