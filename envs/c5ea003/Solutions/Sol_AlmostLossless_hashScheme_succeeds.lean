-- Prove2me | solution 1 for AlmostLossless.hashScheme_succeeds
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T08:13:31.517472+00:00
-- url     : https://prove2.me/submissions/bb2a172b-c201-475c-93f3-c51f491135f0

import Mathlib
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
import Theorems.Thm_AlmostLossless_filter_eq_singleton_of_unique
set_option autoImplicit false
open AlmostLossless

private theorem scan_matches {α : Type*} {M : ℕ} (h : α → Fin M) (i : Fin M)
    (l : List α) : (scanCost h i l).1 = l.filter (fun y => decide (h y = i)) := by
  induction l with
  | nil => rfl
  | cons y ys ih =>
    by_cases hy : h y = i <;> simp [scanCost, hy, ih]

theorem solution {α : Type*} [DecidableEq α] {M : ℕ} {l : List α}
    {h : α → Fin M} {x : α} (hnd : l.Nodup) (hx : x ∈ l)
    (hnc : ¬ ∃ y ∈ l.toFinset, y ≠ x ∧ h y = h x) :
    (hashScheme l h).Succeeds x := by
  letI : Nonempty α := ⟨x⟩
  have huniq : ∀ y ∈ l, h y = h x → y = x := by
    intro y hy hh
    by_contra hne
    exact hnc ⟨y, List.mem_toFinset.mpr hy, hne, hh⟩
  change decodeList h l (h x) = some x
  unfold decodeList
  rw [scan_matches, filter_eq_singleton_of_unique hnd hx huniq]
#print axioms solution
