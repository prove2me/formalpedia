-- Prove2me | Theorems.Thm_gpy_firstMomentCoeff_eq_good_add_defect
-- name    : gpy_firstMomentCoeff_eq_good_add_defect
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-11-01T09:36:43.201346+00:00
-- url     : https://prove2.me/theorems/3e1f6024-4170-49fc-a0a5-6516298aed9f
-- title:
--   First-moment coefficient splits as good part plus defect
-- statement:
--   At every coordinate i, the first-moment coefficient equals the good-part sum plus the defect sum over compatible-but-not-good pairs. Compatibility and goodness are written out in Mathlib terms. Exact identity, not an estimate.
-- source:
--   GPY ratio analysis: threshold, main-term approximations, and BV level cap

import Mathlib
open Classical

theorem gpy_firstMomentCoeff_eq_good_add_defect {k : ℕ} (h : Fin k → ℕ) (R : ℕ) (lam : (Fin k → ℕ) → ℝ) (i : Fin k) : (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), @ite ℝ (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) (Classical.propDecidable _) (lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) 0) = (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), (if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) then lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)) else 0)) + (∑ d ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), ∑ e ∈ ((Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R)), (@ite ℝ ((∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ, h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧ ¬ (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧ Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))) (@instDecidableAnd _ _ (Classical.propDecidable _) (@instDecidableNot _ (Classical.propDecidable _))) (lam d * lam e / Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) 0)) := by sorry
