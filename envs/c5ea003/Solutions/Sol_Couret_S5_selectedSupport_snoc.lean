-- Prove2me | solution 1 for Couret.S5.selectedSupport_snoc
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:16:17.499691+00:00
-- url     : https://prove2.me/submissions/e6a3e536-93c5-4f15-8054-92a7752ff4e0

import Definitions.Def_Couret_SubproductSemantics_e0771d3a736f
import Std
import Theorems.Thm_Couret_Choice_eval_allSkip
import Theorems.Thm_Couret_Choice_eval_of_not_picked
import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5















theorem p2m_local_selectedSupport_snoc (w : Word Code30) (g u : Code30) :
    selectedSupport (.snoc w g) u ↔
      selectedSupport w u ∨ (∃ v, selectedSupport w v ∧ mul30 g v = u) ∨ u = g := by
  constructor
  · rintro ⟨s,hp,he⟩
    cases s with
    | skip s => exact Or.inl ⟨s,hp,he⟩
    | take s =>
      by_cases hs : s.picked
      · exact Or.inr (Or.inl ⟨Choice.eval mod30Product s,⟨s,hs,rfl⟩,
          (mod30Product.comm _ _).trans he⟩)
      · have h0 := Choice.eval_of_not_picked mod30Product s hs
        have hg : Choice.eval mod30Product (.take s g) = g := by
          change mod30Product.mul (Choice.eval mod30Product s) g = g
          rw [h0]; exact mod30Product.one_mul g
        exact Or.inr (Or.inr (he.symm.trans hg))
  · intro h
    rcases h with ⟨s,hp,he⟩ | ⟨v,⟨s,hp,he⟩,hprod⟩ | h
    · exact ⟨.skip s g,hp,he⟩
    · refine ⟨.take s g,True.intro,?_⟩
      change mod30Product.mul (Choice.eval mod30Product s) g = u
      rw [he,mod30Product.comm]; exact hprod
    · refine ⟨.take (Choice.allSkip w) g,True.intro,?_⟩
      change mod30Product.mul (Choice.eval mod30Product (Choice.allSkip w)) g = u
      rw [Choice.eval_allSkip,mod30Product.one_mul]; exact h.symm



end S5
end Couret

theorem solution : ∀ (w : Couret.Word.{0} Couret.Code30) (g u : Couret.Code30),
  Iff (Couret.S5.selectedSupport (@Couret.Word.snoc.{0} Couret.Code30 w g) u)
    (Or (Couret.S5.selectedSupport w u)
      (Or
        (@Exists.{1} Couret.Code30 fun v =>
          And (Couret.S5.selectedSupport w v) (@Eq.{1} Couret.Code30 (Couret.mul30 g v) u))
        (@Eq.{1} Couret.Code30 u g))) := @_root_.Couret.S5.p2m_local_selectedSupport_snoc

