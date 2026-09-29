-- Prove2me | solution 1 for OperadicRealization.ctxEquiv_congruence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T23:48:29.944956+00:00
-- url     : https://prove2.me/submissions/544f8e65-b86f-4b46-916f-89f4e0ed0607

import Mathlib
import Definitions.Def_Bridges_OperadicRealizationDuality
open Function Set OperadicRealization in
theorem solution {S : AlgSignature} {G Obs : Type} (sem : ObsSem S G Obs)
    (op : S.Op) (ts us : Fin (S.arity op) → Term S G)
    (h : ∀ i, ctxEquiv sem (ts i) (us i)) :
    ctxEquiv sem (Term.app op ts) (Term.app op us) := by
  -- plugging into a composite context
  have hcomp : ∀ (c₁ c₂ : Ctx S G) (t : Term S G), (c₁.comp c₂).plug t = c₁.plug (c₂.plug t) := by
    intro c₁ c₂ t
    induction c₁ with
    | hole => rfl
    | app op focus others sub ih =>
      show Term.app op (fun j => if j = focus then (sub.comp c₂).plug t else others j)
        = Term.app op (fun j => if j = focus then sub.plug (c₂.plug t) else others j)
      rw [ih]
  intro c
  -- replace the arguments one at a time
  let v : ℕ → Term S G := fun m => Term.app op (fun j => if (j : ℕ) < m then us j else ts j)
  have hstep : ∀ m, sem (c.plug (v 0)) = sem (c.plug (v m)) := by
    intro m
    induction m with
    | zero => rfl
    | succ m ih =>
      rw [ih]
      by_cases hm : m < S.arity op
      · -- positions `≠ m` agree; position `m` switches from `ts m` to `us m`
        let i : Fin (S.arity op) := ⟨m, hm⟩
        let mix : Fin (S.arity op) → Term S G := fun j => if (j : ℕ) < m then us j else ts j
        have e1 : v m = (Ctx.app op i mix Ctx.hole).plug (ts i) := by
          show Term.app op _ = Term.app op _
          congr 1
          funext j
          by_cases hj : j = i
          · subst hj
            simp [mix, i, Ctx.plug]
          · have hjm : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
            simp [hj, mix]
        have e2 : v (m + 1) = (Ctx.app op i mix Ctx.hole).plug (us i) := by
          show Term.app op _ = Term.app op _
          congr 1
          funext j
          by_cases hj : j = i
          · subst hj
            simp [mix, i, Ctx.plug]
          · have hjm : (j : ℕ) ≠ m := fun h => hj (Fin.ext h)
            have : ((j : ℕ) < m + 1) ↔ ((j : ℕ) < m) := by omega
            simp [hj, mix, this]
        rw [e1, e2, ← hcomp, ← hcomp]
        exact h i _
      · -- past the last argument nothing changes
        have : v (m + 1) = v m := by
          show Term.app op _ = Term.app op _
          congr 1
          funext j
          have h1 : (j : ℕ) < m + 1 := by omega
          have h2 : (j : ℕ) < m := by omega
          simp [h1, h2]
        rw [this]
  have h0 : v 0 = Term.app op ts := by
    show Term.app op _ = Term.app op _
    congr 1
  have hn : v (S.arity op) = Term.app op us := by
    show Term.app op _ = Term.app op _
    congr 1
    funext j
    simp [j.isLt]
  rw [← h0, ← hn]
  exact hstep _
