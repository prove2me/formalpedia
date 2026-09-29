-- Prove2me | solution 1 for ScanSchemeDecoding.ScanScheme.exists_costly_key
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T18:03:40.98068+00:00
-- url     : https://prove2.me/submissions/4a357a01-a3c3-4b97-80e8-67f540658f5a

-- Sol generated from Algebra/ScanSchemeDecoding/Optimum.lean
import Mathlib
import Definitions.Def_Algebra_ScanSchemeDecoding_Core
import Definitions.Def_Algebra_ScanSchemeDecoding_Optimum
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_exists_key_cost_eq_card
import Theorems.Thm_ScanSchemeDecoding_ScanScheme_sum_fiber_card

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







open ScanSchemeDecoding.ScanScheme in
theorem solution(hα : 0 < Fintype.card α) [Nonempty β] :
    ∃ x, Fintype.card α ≤ Fintype.card β * S.decodeCost x := by
  classical
  have hβ : 0 < Fintype.card β := Fintype.card_pos
  -- some bucket carries at least the average load
  have hex : ∃ b : β, Fintype.card α ≤ Fintype.card β * (S.fiber b).card := by
    by_contra hcon
    push_neg at hcon
    have hlt : ∀ b : β, Fintype.card β * (S.fiber b).card ≤ Fintype.card α - 1 :=
      fun b => by have := hcon b; omega
    have h1 : ∑ b : β, Fintype.card β * (S.fiber b).card
        ≤ ∑ _b : β, (Fintype.card α - 1) := Finset.sum_le_sum (fun b _ => hlt b)
    rw [← Finset.mul_sum, S.sum_fiber_card] at h1
    simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at h1
    have : Fintype.card β * Fintype.card α ≤ Fintype.card β * (Fintype.card α - 1) := h1
    have := Nat.le_of_mul_le_mul_left this hβ
    omega
  obtain ⟨b, hb⟩ := hex
  have hne : (S.fiber b).Nonempty := by
    rw [← Finset.card_pos]
    rcases Nat.eq_zero_or_pos (S.fiber b).card with h | h
    · rw [h] at hb; omega
    · exact h
  obtain ⟨x, _, hx⟩ := S.exists_key_cost_eq_card hne
  exact ⟨x, by rw [hx]; exact hb⟩
