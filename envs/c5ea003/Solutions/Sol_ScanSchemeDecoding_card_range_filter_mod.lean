-- Prove2me | solution 1 for ScanSchemeDecoding.card_range_filter_mod
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:08:32.463262+00:00
-- url     : https://prove2.me/submissions/5eb9a5c8-3d92-479b-85e5-9aea0e5092cd

-- Sol generated from Algebra/ScanSchemeDecoding/Optimum.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum

/-!
# The exact optimum of a scan scheme, and the pigeonhole failure analysis

Combining the exact cost accounting of `Algebra.ScanSchemeDecoding.Core` with the
exact pigeonhole optimum of `Algebra.ScanSchemeDecoding.Triangle` we obtain:

* `ScanSchemeDecoding.ScanScheme.triangleOpt_le_decodeCost` — **every** scan scheme on
  `N` keys with `m` bucket labels costs at least `triangleOpt N m`;
* `ScanSchemeDecoding.modScheme_decodeCost` — the residue scheme `x ↦ x % m` costs
  *exactly* `triangleOpt N m`;
* `ScanSchemeDecoding.scan_optimum` — hence `triangleOpt N m` is the least achievable
  total cost (`IsLeast`), an exact optimum rather than a bound;
* `ScanSchemeDecoding.ScanScheme.exists_costly_key` — the failure analysis: some key
  always costs at least the average bucket size, `N ≤ m * decodeCost x`;
* `ScanSchemeDecoding.ScanScheme.two_mul_decodeCost_ge` — the averaged `ε`-form.
-/

open ScanSchemeDecoding

open Finset

open ScanScheme

variable {α β : Type*} [Fintype α] [LinearOrder α] [Fintype β] [DecidableEq β]
variable (S : ScanScheme α β)






/-! ### The residue scheme attains the optimum -/







open ScanSchemeDecoding in
theorem solution{m : ℕ} (hm : 0 < m) {j : ℕ} (hj : j < m) (N : ℕ) :
    ((Finset.range N).filter (fun x => x % m = j)).card
      = N / m + (if j < N % m then 1 else 0) := by
  classical
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    have hnotmem : N ∉ (Finset.range N).filter (fun x => x % m = j) := by
      simp
    -- arithmetic of the successor step
    have hdm : m * (N / m) + N % m = N := Nat.div_add_mod N m
    have hmod : N % m < m := Nat.mod_lt _ hm
    by_cases hfull : N % m + 1 = m
    · have hNsucc : N + 1 = m * (N / m + 1) := by
        rw [Nat.mul_add, Nat.mul_one]; omega
      have hd : (N + 1) / m = N / m + 1 := by
        rw [hNsucc, Nat.mul_div_cancel_left _ hm]
      have hr : (N + 1) % m = 0 := by
        rw [hNsucc]; exact Nat.mul_mod_right _ _
      rw [hd, hr]
      by_cases hjm : N % m = j
      · rw [if_pos hjm, Finset.card_insert_of_notMem hnotmem, ih]
        have : ¬ j < N % m := by omega
        simp [this]
      · rw [if_neg hjm, ih]
        have h1 : j < N % m := by omega
        simp [h1]
    · have hsplit : N + 1 = m * (N / m) + (N % m + 1) := by omega
      have hz : (N % m + 1) / m = 0 := Nat.div_eq_of_lt (by omega)
      have hz' : (N % m + 1) % m = N % m + 1 := Nat.mod_eq_of_lt (by omega)
      have hd : (N + 1) / m = N / m := by
        rw [hsplit, Nat.mul_add_div hm, hz, Nat.add_zero]
      have hr : (N + 1) % m = N % m + 1 := by
        rw [hsplit, Nat.mul_add_mod, hz']
      rw [hd, hr]
      by_cases hjm : N % m = j
      · rw [if_pos hjm, Finset.card_insert_of_notMem hnotmem, ih]
        have h1 : ¬ j < N % m := by omega
        have h2 : j < N % m + 1 := by omega
        simp [h1, h2]
      · rw [if_neg hjm, ih]
        by_cases h1 : j < N % m
        · simp [h1, Nat.lt_succ_of_lt h1]
        · have h2 : ¬ j < N % m + 1 := by omega
          simp [h1, h2]
