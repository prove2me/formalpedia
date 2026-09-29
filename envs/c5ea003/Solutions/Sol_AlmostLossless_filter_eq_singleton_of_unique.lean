-- Prove2me | solution 1 for AlmostLossless.filter_eq_singleton_of_unique
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T11:17:38.223852+00:00
-- url     : https://prove2.me/submissions/3478bd21-760e-4310-b51a-9026002c48bc

import Definitions.Def_Bridges_AlmostLosslessCompression
import Definitions.Def_Bridges_AlmostLosslessRandomCoding
open AlmostLossless in
theorem solution {α : Type*} {M : ℕ} {h : α → Fin M} {l : List α} {x : α}
    (hnd : l.Nodup) (hx : x ∈ l) (huniq : ∀ y ∈ l, h y = h x → y = x) :
    l.filter (fun z => decide (h z = h x)) = [x] := by
  induction l with
  | nil => simp at hx
  | cons a t ih =>
    rw [List.nodup_cons] at hnd
    by_cases hax : a = x
    · subst hax
      have hnil : t.filter (fun z => decide (h z = h a)) = [] := by
        rw [List.filter_eq_nil_iff]
        intro y hy hyh
        have := huniq y (List.mem_cons_of_mem _ hy) (by simpa using hyh)
        exact hnd.1 (this ▸ hy)
      simp [hnil]
    · have hxt : x ∈ t := by
        rcases List.mem_cons.mp hx with h1 | h1
        · exact absurd h1.symm hax
        · exact h1
      have hha : h a ≠ h x := fun hh => hax (huniq a (List.mem_cons_self) hh)
      rw [List.filter_cons, if_neg (by simpa using hha)]
      exact ih hnd.2 hxt (fun y hy hyh => huniq y (List.mem_cons_of_mem _ hy) hyh)
