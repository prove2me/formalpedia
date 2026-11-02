-- Prove2me | Theorems.Thm_gpy_firstMoment_approx
-- name    : gpy_firstMoment_approx
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T09:18:12.197372+00:00
-- url     : https://prove2.me/theorems/2982bde6-00e8-4b64-ac62-264de40fe256
-- title:
--   First-moment approximation by the first-moment coefficient
-- statement:
--   The first-moment sum over an interval equals (y - x) times the first-moment coefficient up to the full lambda-mass, where the coefficient is the 1/L sum over compatible support pairs written out in Mathlib terms.
-- source:
--   GPY ratio analysis: threshold, main-term approximations, and BV level cap

import Mathlib
open Classical

theorem gpy_firstMoment_approx {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (lam : (Fin k → ℕ) → ℝ) {x y : ℕ} (hxy : x ≤ y) : abs ((∑ n ∈ Finset.Ioc x y, ((∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2)) - ((y : ℝ) - x) * (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), @ite ℝ (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) (Classical.propDecidable _) (lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) 0)) ≤ ∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), abs (lam d * lam e) := by sorry
