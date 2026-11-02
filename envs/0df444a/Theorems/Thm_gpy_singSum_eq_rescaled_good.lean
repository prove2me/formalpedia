-- Prove2me | Theorems.Thm_gpy_singSum_eq_rescaled_good
-- name    : gpy_singSum_eq_rescaled_good
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T10:07:34.956321+00:00
-- url     : https://prove2.me/theorems/ee4bd25a-87ce-4ff4-8aa5-2708e8181333
-- title:
--   Singular sum is the (L/phi(L))-rescaled good part
-- statement:
--   The singular sum at coordinate i equals the good-restricted sum with each good pair's 1/L term rescaled by L/phi(L). Goodness and the support are written out in Mathlib terms. Exact identity; no inequality between the singular sum and the coefficient follows from it alone.
-- source:
--   GPY ratio analysis: threshold, main-term approximations, and BV level cap

import Mathlib
open Classical

theorem gpy_singSum_eq_rescaled_good {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (lam : (Fin k → ℕ) → ℝ) (i : Fin k) : (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then lam d * lam e / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ) else 0) = ∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then (((Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) : ℕ) : ℝ) / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)) * (lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) else 0) := by sorry
