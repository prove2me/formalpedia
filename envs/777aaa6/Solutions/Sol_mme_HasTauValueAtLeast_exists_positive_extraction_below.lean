-- Prove2me | solution 1 for mme_HasTauValueAtLeast_exists_positive_extraction_below
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T06:45:09.980521+00:00
-- url     : https://prove2.me/submissions/582f74a1-860b-4a35-b160-d6993707f47a

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Definitions.Def_mme_tau_value

open Filter BigOperators
open MME

set_option autoImplicit false
set_option warningAsError true

universe u

theorem solution
    {K : Type u} [Field K]
    (T : TensorObj K 3) (tau B V : ℝ)
    (hB : 0 < B) (hV : 0 ≤ V) (hVB : V < B)
    (h : HasTauValueAtLeast T tau B) :
    ∃ e : ℕ, 0 < e ∧
      ∃ (k : ℕ) (a b c : Fin k → ℕ),
        TensorObj.Restrict
          (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
          (T.kronPow e) ∧
        V ^ e ≤ ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := by
  have hratio : V / B < 1 := (div_lt_one hB).2 hVB
  have hepsilon : 0 < 1 - V / B := sub_pos.mpr hratio
  have hfrequent := h.2 (1 - V / B) hepsilon
  obtain ⟨e, hextract, hepos⟩ :=
    (hfrequent.and_eventually (eventually_gt_atTop 0)).exists
  obtain ⟨k, a, b, c, hrestrict, hweight⟩ := hextract
  refine ⟨e, hepos, k, a, b, c, hrestrict, ?_⟩
  obtain ⟨n, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hepos)
  have hpowers : V ^ n ≤ B ^ n :=
    pow_le_pow_left₀ hV hVB.le n
  calc
    V ^ (n + 1) = V * V ^ n := pow_succ' V n
    _ ≤ V * B ^ n := mul_le_mul_of_nonneg_left hpowers hV
    _ = B ^ (n + 1) * (1 - (1 - V / B)) := by
      field_simp [ne_of_gt hB]
      ring
    _ ≤ ∑ i, (((a i * b i * c i : ℕ) : ℝ) ^ tau) := hweight

