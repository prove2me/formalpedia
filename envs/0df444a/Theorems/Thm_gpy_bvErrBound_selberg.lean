-- Prove2me | Theorems.Thm_gpy_bvErrBound_selberg
-- name    : gpy_bvErrBound_selberg
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T19:04:04.361244+00:00
-- url     : https://prove2.me/theorems/f6102faa-a68d-42a2-99b7-820a2086bb14
-- title:
--   Selberg chained BV error bound
-- statement:
--   Let h be a tuple of shifts, R a level, deg a degree, and x <= y. Let the Selberg weight be lam_d = mu(prod d) * (1 - log(prod d)/log R)^deg when prod d <= R, and 0 otherwise. Under Bombieri-Vinogradov-style sum bounds (with constant C >= 0, parameters eta and A', and model li), the level conditions R^2 < (y + h_i)^(1/2 - eta) and R^2 < (x + h_i)^(1/2 - eta), and 2 <= y + h_i, 2 <= x + h_i for every coordinate i, the absolute difference between the second moment with the Selberg weight and its BV main term for the model li/phi is at most the tau-weighted mass squared (the square of sum_{D in [1, R]} tau_k(D) * |mu(D) * (1 - log D/log R)^deg|) times (R^2 times the sum over i of the BV endpoint error terms plus k). This is the chained bound with the tau-weighted mass, not a separating bound: separation of the main term from the error remains open and is not claimed here.
-- source:
--   GPY Selberg weights: the chained second-moment BV error bound with the tau-weighted Selberg mass, chaining the BV instantiation bound with the tau-weighted mass identity

import Mathlib
open Classical

theorem gpy_bvErrBound_selberg {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (deg : ℕ) {x y : ℕ} (hxy : x ≤ y)
    {η A' C : ℝ} (hC : 0 ≤ C) (li : ℝ → ℝ)
    (hBV : ∀ Y' : ℕ, 2 ≤ Y' → (R : ℝ) ^ 2 < (Y' : ℝ) ^ (1 / 2 - η) →
      ∀ v : ℕ → ℕ, (∀ q, Nat.Coprime (v q) q) →
      ∑ q ∈ (Finset.range ⌈(Y' : ℝ) ^ (1 / 2 - η)⌉₊).filter
          (fun q : ℕ => 1 ≤ q ∧ (q : ℝ) < (Y' : ℝ) ^ (1 / 2 - η)),
        abs (((((Finset.range (Y' + 1)).filter
          (fun p => Nat.Prime p ∧ p ≡ v q [MOD q])).card : ℝ))
          - li (Y' : ℝ) / (Nat.totient q : ℝ))
          ≤ C * ((Y' : ℝ) * Real.log (Y' : ℝ) ^ (-A')))
    (hlevel : ∀ i, (R : ℝ) ^ 2 < ((y + h i : ℕ) : ℝ) ^ (1 / 2 - η) ∧
      (R : ℝ) ^ 2 < ((x + h i : ℕ) : ℝ) ^ (1 / 2 - η))
    (hY2 : ∀ i, 2 ≤ y + h i ∧ 2 ≤ x + h i) :
    abs (∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then
            (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
            else 0) else 0) ^ 2
      - ∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if ∏ i, d i ≤ R then
            (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
              * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
          else 0)
        * (if ∏ i, e i ≤ R then
            (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
              * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
          else 0)
        * (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i)
                (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            then li ((y + h i : ℕ) : ℝ)
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
              - li ((x + h i : ℕ) : ℝ)
              / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
            else 0))
      ≤ (∑ D ∈ Finset.Icc 1 R,
          (((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 D)).filter
            (fun d => ∏ i, d i = D)).card : ℝ)
            * |(ArithmeticFunction.moebius D : ℝ)
              * (1 - Real.log D / Real.log R) ^ deg|) ^ 2
        * ((R : ℝ) ^ 2 * (∑ i, (C * (((y + h i : ℕ) : ℝ)
            * Real.log ((y + h i : ℕ) : ℝ) ^ (-A'))
          + C * (((x + h i : ℕ) : ℝ)
            * Real.log ((x + h i : ℕ) : ℝ) ^ (-A')))) + (k : ℝ)) := by sorry
