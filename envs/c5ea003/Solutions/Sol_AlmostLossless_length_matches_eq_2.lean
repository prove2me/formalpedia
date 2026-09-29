-- Prove2me | solution 2 for AlmostLossless.length_matches_eq
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T11:12:13.010763+00:00
-- url     : https://prove2.me/submissions/8e56b652-a514-464b-8382-0e61a4b7d6f7

import Definitions.Def_Bridges_AlmostLosslessListDecoding
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
open AlmostLossless in
theorem solution {α : Type*} [DecidableEq α] {M : ℕ} (h : α → Fin M) {l : List α} (hnd : l.Nodup)
    {x : α} (hx : x ∈ l) :
    ((scanCost h (h x) l).1).length
      = (collisionSet (fun _ : Fin 1 => h) 0 l.toFinset x).card + 1 := by
  have hscan : ∀ (i : Fin M) (l : List α), (scanCost h i l).1 = l.filter (fun y => decide (h y = i)) := by
    intro i l
    induction l with
    | nil => rfl
    | cons a t ih =>
      simp only [scanCost, List.filter_cons, ih]
      split_ifs <;> simp_all
  rw [hscan]
  have hnd' : (l.filter (fun y => decide (h y = h x))).Nodup := hnd.filter _
  rw [← List.toFinset_card_of_nodup hnd', List.toFinset_filter]
  unfold collisionSet
  rw [Finset.filter_erase, Finset.card_erase_of_mem (by simp [hx])]
  have hpos : 0 < (l.toFinset.filter (fun y => decide (h y = h x) = true)).card :=
    Finset.card_pos.mpr ⟨x, by simp [hx]⟩
  simp only [decide_eq_true_eq] at hpos ⊢
  omega
