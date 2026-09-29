-- Prove2me | solution 1 for F1Tightness.scanCost_lt_polCost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:13:59.805378+00:00
-- url     : https://prove2.me/submissions/bbac0cf7-3051-44ca-ad22-7384d99e8fda

-- Sol generated from Probability/F1TightnessUniqueness.lean
import Mathlib
import Definitions.Def_Probability_F1TightnessCore
import Theorems.Thm_F1Tightness_perm_eq_one_of_strictMono

/-!
# Uniqueness of the optimal scan policy (paper 250)

`Probability.F1TightnessCore` shows that on an antitone profile the ascending
scan minimises the expected probe count, so its speed-up `S_asc = 1/Λ` is the
best realizable one and the master bound overshoots it by the factor `X`.  Here
we sharpen that statement: on a *strictly* front-loaded profile the ascending
scan is the **unique** minimiser, so the quantity `S_asc` compared with the
bound is not an artefact of a particular tie-breaking among optimal policies.

Main results.

* `perm_eq_one_of_strictMono` — a strictly monotone permutation of `Fin M` is
  the identity (hence a non-identity policy always has an inversion).
* `scanCost_lt_polCost` — strict rearrangement: every policy other than the
  ascending one is strictly more expensive on a strictly antitone profile.
* `polCost_eq_scanCost_iff` — the optimal policy is unique.
* `speedup_lt_Sasc` — consequently the ascending speed-up strictly dominates
  every other policy, and (with `F1Tightness.speedup_lt_bound`) still falls
  short of the master bound by the factor `X`.
-/

open Finset

open F1Tightness

variable {M : ℕ}


/-- A non-identity policy has an inversion. -/
theorem exists_inversion {σ : Equiv.Perm (Fin M)} (hσ : σ ≠ 1) :
    ∃ i j : Fin M, i < j ∧ σ j < σ i := by
  by_contra hcon
  push_neg at hcon
  refine hσ (perm_eq_one_of_strictMono ?_)
  intro i j hij
  rcases lt_or_eq_of_le (hcon i j hij) with h | h
  · exact h
  · exact absurd (σ.injective h) (ne_of_lt hij)





open F1Tightness in
theorem solution{p : Fin M → ℝ} (hanti : StrictAnti p)
    {σ : Equiv.Perm (Fin M)} (hσ : σ ≠ 1) : scanCost p < polCost p σ := by
  have hav : Antivary p (fun i : Fin M => (((i : ℕ) : ℝ) + 1)) := by
    intro i j hij
    have hlt : i < j := by
      by_contra hji
      push_neg at hji
      have : ((j : ℕ) : ℝ) ≤ ((i : ℕ) : ℝ) := by
        exact_mod_cast Fin.le_iff_val_le_val.mp hji
      simp only at hij
      linarith
    exact (hanti hlt).le
  obtain ⟨i, j, hij, hσij⟩ := exists_inversion hσ
  have hnot : ¬ Antivary p ((fun i : Fin M => (((i : ℕ) : ℝ) + 1)) ∘ (σ : Fin M → Fin M)) := by
    intro hA
    have hlt : (((σ j : ℕ) : ℝ) + 1) < (((σ i : ℕ) : ℝ) + 1) := by
      have : ((σ j : ℕ) : ℝ) < ((σ i : ℕ) : ℝ) := by exact_mod_cast hσij
      linarith
    have := hA hlt
    exact absurd (hanti hij) (not_lt.mpr this)
  have hkey := (hav.sum_smul_lt_sum_smul_comp_perm_iff (σ := σ)).2 hnot
  simp only [smul_eq_mul] at hkey
  unfold scanCost polCost
  calc ∑ i : Fin M, (((i : ℕ) : ℝ) + 1) * p i
      = ∑ i : Fin M, p i * (((i : ℕ) : ℝ) + 1) := Finset.sum_congr rfl fun i _ => by ring
    _ < ∑ i : Fin M, p i * (((σ i : ℕ) : ℝ) + 1) := hkey
    _ = ∑ i : Fin M, (((σ i : ℕ) : ℝ) + 1) * p i :=
        Finset.sum_congr rfl fun i _ => by ring
