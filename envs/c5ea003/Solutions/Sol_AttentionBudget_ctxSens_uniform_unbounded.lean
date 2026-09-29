-- Prove2me | solution 1 for AttentionBudget.ctxSens_uniform_unbounded
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-09T20:18:35.717488+00:00
-- url     : https://prove2.me/submissions/0e428c4c-ce8b-40b6-a13f-c0c6f78fd383

-- Sol generated from Shared/AttentionBudgetKnee.lean
import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
import Theorems.Thm_AttentionBudget_kstar_uniform_ge
import Theorems.Thm_AttentionBudget_kstar_le_of_pass

open AttentionBudget
open Finset

lemma uniform_pos : ∀ i : ℕ, (0 : ℝ) < (fun _ => (1 : ℝ)) i := fun _ => one_pos

lemma retained_uniform' (n k : ℕ) :
    retained (fun _ => (1 : ℝ)) n k = (min k n : ℝ) / n := by
  simp [retained, headMass]

lemma kstar_uniform_le' {τ : ℝ} {n : ℕ} (hn : 0 < n) (hτ : τ ≤ 1) :
    kstar (fun _ => (1 : ℝ)) n τ ≤ ⌈τ * n⌉₊ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hle : ⌈τ * n⌉₊ ≤ n := Nat.ceil_le.mpr (by nlinarith)
  apply kstar_le_of_pass
  have hleR : ((⌈τ * n⌉₊ : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hle
  rw [retained_uniform', min_eq_left hleR, le_div_iff₀ hnR]
  exact Nat.le_ceil _

variable {w : ℕ → ℝ} (hw : ∀ i, 0 < w i)
include hw
variable {w : ℕ → ℝ} {τ : ℝ} {n : ℕ} (hw : ∀ i, 0 < w i)
include hw
variable {w : ℕ → ℝ} {r τ : ℝ}
variable {w : ℕ → ℝ} {τ : ℝ} {n : ℕ}

open AttentionBudget in
theorem solution (hτ0 : 0 < τ) (hτ : τ ≤ 1) (K : ℕ) :
    ∃ n : ℕ, 0 < n ∧ K < ctxSens (fun _ => (1 : ℝ)) τ n := by
  obtain ⟨m, hm⟩ := exists_nat_gt ((K + 3 : ℝ) / τ)
  refine ⟨max m 1, by omega, ?_⟩
  set n := max m 1 with hn
  have hn0 : 0 < n := by omega
  have hnR : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_max_left m 1
  have hbig : (K : ℝ) + 3 ≤ τ * n := by
    rw [div_lt_iff₀ hτ0] at hm
    nlinarith
  have hlow : τ * (2 * n : ℝ) ≤ (kstar (fun _ => (1 : ℝ)) (2 * n) τ : ℝ) := by
    have := @kstar_uniform_ge (fun _ => (1 : ℝ)) uniform_pos τ (2 * n) (by omega) hτ
    push_cast at this ⊢
    linarith
  have hhigh : (kstar (fun _ => (1 : ℝ)) n τ : ℝ) ≤ τ * n + 1 := by
    have h1 := kstar_uniform_le' hn0 hτ
    have h2 : ((⌈τ * n⌉₊ : ℕ) : ℝ) ≤ τ * n + 1 := by
      have := Nat.ceil_lt_add_one (a := τ * (n : ℝ)) (by positivity)
      linarith
    have h3 : ((kstar (fun _ => (1 : ℝ)) n τ : ℕ) : ℝ) ≤ ((⌈τ * n⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast h1
    linarith
  have hgap : (kstar (fun _ => (1 : ℝ)) n τ : ℝ) + (K + 1) ≤
      (kstar (fun _ => (1 : ℝ)) (2 * n) τ : ℝ) := by nlinarith
  have hgapN : kstar (fun _ => (1 : ℝ)) n τ + (K + 1) ≤ kstar (fun _ => (1 : ℝ)) (2 * n) τ := by
    exact_mod_cast hgap
  simp only [ctxSens]
  omega
