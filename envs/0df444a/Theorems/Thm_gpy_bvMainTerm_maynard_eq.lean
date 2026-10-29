-- Prove2me | Theorems.Thm_gpy_bvMainTerm_maynard_eq
-- name    : gpy_bvMainTerm_maynard_eq
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T21:42:15.537752+00:00
-- url     : https://prove2.me/theorems/a678b9d9-67ab-493c-b0d1-93912549f9e8
-- title:
--   Maynard main term: exact coefficient identification
-- statement:
--   Let h be a tuple of shifts, R a level, m a degree, li a real function, and x, y interval endpoints. Let the Maynard weight be lam_d = (product over i of mu(d_i)) times the polynomial simplex cutoff (1 - sum_i log(d_i)/log R)^m when sum_i log(d_i)/log R <= 1, and 0 otherwise. Then the BV main term for the model M(Y, L) = li(Y)/phi(L) with the Maynard weights (the sum over support pairs (d, e) of lam_d * lam_e times the model difference at the interval endpoints over good pairs, where a pair is good at coordinate i when some witness w of the joint divisibility system has w + h_i coprime to the combined modulus L) equals the sum over support pairs of lam_d * lam_e times the sum over coordinates i of, for good pairs, (li(y + h_i) - li(x + h_i)) / phi(L), and 0 for bad pairs. In other words, evaluating this coefficient IS the singular-series step: nothing else stands between it and the main term. Honest scope note: the Maynard–Tao polynomial-subcase candidate does NOT close the GPY argument. Its singular-series evaluation (identifying the main-term coefficient with the singular series times the cutoff integral) still needs Mertens-type sum-to-integral estimates, local-factor computations, and tau-weighted divisor sums, and the sharp tau-weighted lambda-mass bound is likewise open. These are foundation and coefficient-identification results, not a separation claim; for the qualitative GPY conclusion (liminf gap/log -> 0) the Maynard machinery is arguably overkill.
-- source:
--   GPY Maynard-Tao weights (polynomial subcase): the exact coefficient identification of the BV main term for the model li/phi

import Mathlib
open Classical

theorem gpy_bvMainTerm_maynard_eq {k : ℕ} (h : Fin k → ℕ) (R m : ℕ)
    (li : ℝ → ℝ) (x y : ℕ) :
    (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ((∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
            (if ∑ i, Real.log (d i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (d i) / Real.log R) ^ m else 0))
          * ((∏ i, (ArithmeticFunction.moebius (e i) : ℝ)) *
            (if ∑ i, Real.log (e i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (e i) / Real.log R) ^ m else 0))
          * (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
              then li ((y + h i : ℕ) : ℝ)
                / (Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ)
                - li ((x + h i : ℕ) : ℝ)
                / (Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ)
              else 0))
      = ∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ((∏ i, (ArithmeticFunction.moebius (d i) : ℝ)) *
            (if ∑ i, Real.log (d i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (d i) / Real.log R) ^ m else 0))
          * ((∏ i, (ArithmeticFunction.moebius (e i) : ℝ)) *
            (if ∑ i, Real.log (e i) / Real.log R ≤ 1 then
              (1 - ∑ i, Real.log (e i) / Real.log R) ^ m else 0))
          * (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
                Nat.Coprime (w + h i)
                  (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
              then (li (y + h i) - li (x + h i))
                * ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ))⁻¹
              else 0) := by sorry
