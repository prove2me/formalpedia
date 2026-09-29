-- Prove2me | solution 1 for CRTSplitNoGo.sum_closureTime_eq_sum_card
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T15:44:09.167119+00:00
-- url     : https://prove2.me/submissions/1137139f-74d1-4699-a16c-64fec0631837

import Mathlib
import Definitions.Def_Bridges_CRTSplitNoGoAverage
import Definitions.Def_Bridges_CRTSplitNoGoBirthday
open CRTSplitNoGo Finset in
theorem solution {α : Type*} [Fintype α] [DecidableEq α] (a : α) :
    ∑ f : α → α, closureTime a f
      = ∑ T ∈ Finset.range (Fintype.card α), (injPrefixFinset a T).card := by
  -- collision-freeness of the orbit prefix is downward closed ...
  have hmono : ∀ (f : α → α) (T T' : ℕ), T' ≤ T → InjPrefix f a T → InjPrefix f a T' :=
    fun f T T' h hT i hi j hj => hT i (hi.trans h) j (hj.trans h)
  -- ... and fails at `T = |α|` by pigeonhole (`|α| + 1` orbit points)
  have hN : ∀ f : α → α, ¬ InjPrefix f a (Fintype.card α) := by
    intro f hf
    have hinj : Function.Injective (fun i : Fin (Fintype.card α + 1) => orb f a i) :=
      fun i j h => Fin.ext (hf i (Nat.lt_succ_iff.mp i.isLt) j (Nat.lt_succ_iff.mp j.isLt) h)
    have := Fintype.card_le_of_injective _ hinj
    simp at this
  -- so the closure time counts the collision-free prefix lengths below `|α|`
  have hct : ∀ f : α → α, closureTime a f
      = ((range (Fintype.card α)).filter (fun T => InjPrefix f a T)).card := by
    intro f
    have hne : {T : ℕ | ¬ InjPrefix f a T}.Nonempty := ⟨Fintype.card α, hN f⟩
    have hmem : ¬ InjPrefix f a (closureTime a f) := Nat.sInf_mem hne
    have hle : closureTime a f ≤ Fintype.card α := Nat.sInf_le (hN f)
    have hset : (range (Fintype.card α)).filter (fun T => InjPrefix f a T)
        = range (closureTime a f) := by
      ext T
      simp only [mem_filter, mem_range]
      constructor
      · rintro ⟨-, hinj⟩
        by_contra hlt
        push_neg at hlt
        exact hmem (hmono f T _ hlt hinj)
      · intro hT
        refine ⟨lt_of_lt_of_le hT hle, ?_⟩
        by_contra hc
        exact absurd (Nat.sInf_le hc) (not_le.mpr hT)
    rw [hset, card_range]
  simp_rw [hct, card_filter]
  rw [sum_comm]
  refine sum_congr rfl (fun T _ => ?_)
  rw [injPrefixFinset, card_filter]
