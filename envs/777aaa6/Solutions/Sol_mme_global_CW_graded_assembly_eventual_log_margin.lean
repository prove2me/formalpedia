-- Prove2me | solution 1 for mme_global_CW_graded_assembly_eventual_log_margin
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-30T08:55:41.516984+00:00
-- url     : https://prove2.me/submissions/c43c866e-680b-432e-b0cf-7e1785a11b21

import Definitions.Def_mme_global_CW_graded_start_data
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

open BigOperators MME MME.ProfiledCW MME.GlobalCW MME.RegionRealization
set_option autoImplicit false

theorem solution
    (blockSize ell parts degree : ℕ) (globalRate regionalRate volumeRate tau : ℝ)
    (htau : 0 ≤ tau)
    (hgap : (blockSize : ℝ) * Real.log 7 <
      globalRate + regionalRate + tau * volumeRate) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k → ∀ n : ℕ, k ^ 2 ≤ n →
      ∀ (size : Fin parts → ℕ)
        (positions : ((j : Fin parts) × Fin (size j)) ≃ Fin (blockSize * n))
        (T : ∀ j, Predicate (size j))
        (steps : ∀ j, GlobalCW.Part (size j) ell (T j))
        (Q : Predicate (blockSize * n))
        (target : ∀ i x, Q i x → ∀ j, T j i (fun r ↦ x (positions ⟨j, r⟩)))
        (next : LogJointRecipeG (blockSize * n) ell Q),
      (∀ j, 1 ≤ (steps j).inputs ∧ (steps j).inputs ≤ (k + 1) ^ degree) →
      1 ≤ next.inputs → next.inputs ≤ (k + 1) ^ degree →
      1 ≤ next.a * next.b * next.c →
      (n : ℝ) * globalRate ≤ ∑ j, (steps j).rate →
      (n : ℝ) * regionalRate ≤ next.logOutputs →
      (n : ℝ) * volumeRate ≤ Real.log ((next.a * next.b * next.c : ℕ) : ℝ) →
      ∃ D : GlobalCW.StartG (blockSize * n) ell,
        0 < n ∧ 1 ≤ D.inputs ∧ 1 ≤ D.a * D.b * D.c ∧
        Real.log (D.inputs : ℝ) + ((blockSize * n : ℕ) : ℝ) * Real.log 7 <
          D.logOutputs + tau * Real.log ((D.a * D.b * D.c : ℕ) : ℝ) := by
  let gap := globalRate + regionalRate + tau * volumeRate -
    (blockSize : ℝ) * Real.log 7
  have hgap0 : 0 < gap := sub_pos.mpr hgap
  let H : ℕ := degree * (parts + 1)
  obtain ⟨k0, hk0⟩ := exists_nat_gt ((H : ℝ) / gap)
  refine ⟨max 1 k0, ?_⟩
  intro k hk n hn size positions T steps Q target next hsteps hnext hnextPoly
    hdims hglobal hregional hvolume
  have hk1 : 1 ≤ k := (le_max_left _ _).trans hk
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hk1)
  have hnpos : 0 < n := (pow_pos (by omega : 0 < k) 2).trans_le hn
  have hlarge : (H : ℝ) < gap * k := by
    have hkk : (k0 : ℝ) ≤ k := by exact_mod_cast (le_max_right 1 k0).trans hk
    have hh := (div_lt_iff₀ hgap0).mp (hk0.trans_le hkk)
    simpa [mul_comm] using hh
  let D : GlobalCW.StartG (blockSize * n) ell := {
    parts := parts
    size := size
    positions := positions
    T := T
    steps := steps
    Q := Q
    target := target
    next := next }
  have hinputs : 1 ≤ D.inputs := by
    change 1 ≤ (∏ j, (steps j).inputs) * next.inputs
    simpa using Nat.mul_le_mul (Finset.one_le_prod' (fun j _ ↦ (hsteps j).1)) hnext
  have hpoly : D.inputs ≤ (k + 1) ^ H := by
    change (∏ j, (steps j).inputs) * next.inputs ≤ _
    calc
      _ ≤ (∏ _j : Fin parts, (k + 1) ^ degree) * (k + 1) ^ degree :=
        Nat.mul_le_mul (Finset.prod_le_prod' (fun j _ ↦ (hsteps j).2)) hnextPoly
      _ = (k + 1) ^ H := by
        simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul,
          ← pow_add]
        congr 1
  have hlog : Real.log (D.inputs : ℝ) ≤ (H : ℝ) * k := by
    have hI : (0 : ℝ) < D.inputs := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hinputs)
    have hb : (D.inputs : ℝ) ≤ ((k : ℝ) + 1) ^ H := by exact_mod_cast hpoly
    have hh := Real.log_le_log hI hb
    rw [Real.log_pow] at hh
    have hlogk : Real.log ((k : ℝ) + 1) ≤ k := by
      simpa using Real.log_le_sub_one_of_pos (show 0 < (k : ℝ) + 1 by positivity)
    exact hh.trans (mul_le_mul_of_nonneg_left hlogk (Nat.cast_nonneg H))
  have hcost : Real.log (D.inputs : ℝ) < gap * n := by
    have hh := mul_lt_mul_of_pos_right hlarge hkpos
    have hscale : (k : ℝ) ^ 2 ≤ n := by exact_mod_cast hn
    have hh2 := mul_le_mul_of_nonneg_left hscale hgap0.le
    apply hlog.trans_lt
    nlinarith
  refine ⟨D, hnpos, hinputs, hdims, ?_⟩
  have houtput : (n : ℝ) * (globalRate + regionalRate) ≤ D.logOutputs := by
    change _ ≤ (∑ j, (steps j).rate) + next.logOutputs
    nlinarith
  have hvol := mul_le_mul_of_nonneg_left hvolume htau
  change Real.log (D.inputs : ℝ) + ((blockSize * n : ℕ) : ℝ) * Real.log 7 <
    D.logOutputs + tau * Real.log ((next.a * next.b * next.c : ℕ) : ℝ)
  rw [Nat.cast_mul]
  dsimp [gap] at hcost
  nlinarith

