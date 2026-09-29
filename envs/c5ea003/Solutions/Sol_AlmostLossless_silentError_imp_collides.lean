-- Prove2me | solution 1 for AlmostLossless.silentError_imp_collides
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T11:27:33.976712+00:00
-- url     : https://prove2.me/submissions/8671d376-dc5f-4074-9d0e-48aff61d5c57

import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
open AlmostLossless in
theorem solution {α : Type*} [DecidableEq α] {M : ℕ} {l : List α} {h : α → Fin M} {x : α}
    (hs : (hashScheme l h).SilentError x) :
    ∃ y ∈ l.toFinset, y ≠ x ∧ h y = h x := by
  have hscan : ∀ (i : Fin M) (l : List α),
      (scanCost h i l).1 = l.filter (fun y => decide (h y = i)) := by
    intro i l
    induction l with
    | nil => rfl
    | cons a t ih =>
      simp only [scanCost, List.filter_cons, ih]
      split_ifs <;> simp_all
  obtain ⟨y, hy, hne⟩ := hs
  have hy' : decodeList h l (h x) = some y := hy
  unfold decodeList at hy'
  split at hy'
  next y' heq =>
    have hyy : y' = y := Option.some.inj hy'
    subst hyy
    rw [hscan] at heq
    have hmem : y' ∈ l.filter (fun z => decide (h z = h x)) := by rw [heq]; simp
    rw [List.mem_filter] at hmem
    exact ⟨y', List.mem_toFinset.mpr hmem.1, hne, by simpa using hmem.2⟩
  next => simp at hy'
