-- Prove2me | solution 1 for Couret.properSupport_snoc
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:47:34.251912+00:00
-- url     : https://prove2.me/submissions/13db92e2-6ae0-4732-869d-3b754f3f315c

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
import Theorems.Thm_Couret_Choice_eval_allSkip
import Theorems.Thm_Couret_Choice_eval_of_not_omitted
import Theorems.Thm_Couret_Choice_eval_of_not_picked
import Std

/-!
COU-87, first semantic formalization, 2026-10-30.
The denotation uses independent choices of labeled occurrences, not the automaton
recurrence. Snoc words make appending an occurrence explicit. No assumption of
distinct factors is made. This file does not certify the 147/101 finite tables.
-/

universe u
namespace Couret





variable {α : Type u}







namespace Choice













theorem eval_allTake (M : CMonoid α) (w : Word α) :
    eval M (allTake w) = total M w := by
  induction w with
  | empty => rfl
  | snoc w g ih => exact congrArg (fun x => M.mul x g) ih

theorem allTake_picked (w : Word α) : picked (allTake w) ↔ w.nonempty := by
  cases w <;> simp [allTake, picked, Word.nonempty]

theorem allSkip_omitted (w : Word α) : omitted (allSkip w) ↔ w.nonempty := by
  cases w <;> simp [allSkip, omitted, Word.nonempty]















end Choice











theorem p2m_local_properSupport_snoc (M : CMonoid α) (w : Word α) (hw : w.nonempty)
    (g u : α) :
    properSupport M (.snoc w g) u ↔
      properSupport M w u ∨
      (∃ v, properSupport M w v ∧ M.mul g v = u) ∨
      u = total M w ∨ u = g := by
  constructor
  · rintro ⟨s, hp, ho, hu⟩
    cases s with
    | skip s =>
      by_cases hs : s.omitted
      · exact Or.inl ⟨s, hp, hs, hu⟩
      · exact Or.inr (Or.inr (Or.inl
          (hu.symm.trans (Choice.eval_of_not_omitted M s hs))))
    | take s =>
      by_cases hs : s.picked
      · exact Or.inr (Or.inl ⟨Choice.eval M s, ⟨s, hs, ho, rfl⟩,
          (M.comm g (Choice.eval M s)).trans hu⟩)
      · apply Or.inr; apply Or.inr; apply Or.inr
        calc
          u = M.mul (Choice.eval M s) g := hu.symm
          _ = M.mul M.one g := congrArg (fun x => M.mul x g) (Choice.eval_of_not_picked M s hs)
          _ = g := M.one_mul g
  · intro h
    rcases h with h | h | h | h
    · rcases h with ⟨s, hp, ho, hu⟩
      exact ⟨.skip s g, hp, True.intro, hu⟩
    · rcases h with ⟨v, ⟨s, hp, ho, hv⟩, hu⟩
      refine ⟨.take s g, True.intro, ho, ?_⟩
      exact (congrArg (fun x => M.mul x g) hv).trans ((M.comm v g).trans hu)
    · exact ⟨.skip (Choice.allTake w) g,
        (Choice.allTake_picked w).mpr hw, True.intro,
        (Choice.eval_allTake M w).trans h.symm⟩
    · refine ⟨.take (Choice.allSkip w) g, True.intro,
        (Choice.allSkip_omitted w).mpr hw, ?_⟩
      exact (congrArg (fun x => M.mul x g) (Choice.eval_allSkip M w)).trans
        ((M.one_mul g).trans h.symm)



























/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret


universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} (M : Couret.CMonoid.{p2m_u_0} α) (w : Couret.Word.{p2m_u_0} α),
  @Couret.Word.nonempty.{p2m_u_0} α w →
    ∀ (g u : α),
      Iff (@Couret.properSupport.{p2m_u_0} α M (@Couret.Word.snoc.{p2m_u_0} α w g) u)
        (Or (@Couret.properSupport.{p2m_u_0} α M w u)
          (Or
            (@Exists.{p2m_u_0 + 1} α fun v =>
              And (@Couret.properSupport.{p2m_u_0} α M w v)
                (@Eq.{p2m_u_0 + 1} α (@Couret.CMonoid.mul.{p2m_u_0} α M g v) u))
            (Or (@Eq.{p2m_u_0 + 1} α u (@Couret.total.{p2m_u_0} α M w)) (@Eq.{p2m_u_0 + 1} α u g)))) := @_root_.Couret.p2m_local_properSupport_snoc

