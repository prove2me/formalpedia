-- Prove2me | solution 1 for Couret.S5.full_equals_proper_of_six
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:41:13.387973+00:00
-- url     : https://prove2.me/submissions/aba136fd-0ba9-4c15-8bf1-cfa572cbc7ad

import Definitions.Def_Couret_DavenportThreshold_ac37b2f8de8c
import Std
import Theorems.Thm_Couret_Choice_eval_mul_complement
import Theorems.Thm_Couret_Choice_omitted_complement
import Theorems.Thm_Couret_Choice_picked_complement
import Theorems.Thm_Couret_S5_rank_facts
import Theorems.Thm_Couret_S5_rank_initial
import Theorems.Thm_Couret_S5_subRun_bound
import Theorems.Thm_Couret_S5_subRun_exact
import Theorems.Thm_Couret_fullSupport_iff
import Definitions.Def_Couret_RankBlock00_bd2f9788729f
namespace Couret
namespace S5

theorem rank_progress (w : Word Code30) : min (length w) 5 ≤ rank (subRun w) := by
  induction w with
  | empty => change min 0 5 ≤ rank 0; rw [rank_initial]; decide
  | snoc w g ih =>
    have ht : min (rank (subRun w) + 1) 5 ≤ rank (subStep (subRun w) g) :=
      (rank_facts ⟨subRun w,subRun_bound w⟩).2.2 g
    change min (length w + 1) 5 ≤ rank (subStep (subRun w) g)
    omega



theorem davenport_bound_five : DavenportBound 5 := by
  intro w hw
  have hl := rank_progress w
  have facts : RankFacts (subRun w) := rank_facts ⟨subRun w,subRun_bound w⟩
  have hb := facts.1
  have he : rank (subRun w) = 5 := by omega
  exact (subRun_exact w (0,0)).mp (facts.2.1.mp he)











theorem proper_identity_of_six (w : Word Code30) (hw : 6 ≤ length w) :
    properSupport mod30Product w (0,0) := by
  cases w with
  | empty => change 6 ≤ 0 at hw; omega
  | snoc w g =>
    have h5 : 5 ≤ length w := by change 6 ≤ length w + 1 at hw; omega
    rcases davenport_bound_five w h5 with ⟨s,hp,he⟩
    exact ⟨.skip s g,hp,True.intro,he⟩

theorem proper_total_of_six (w : Word Code30) (hw : 6 ≤ length w) :
    properSupport mod30Product w (total mod30Product w) := by
  rcases proper_identity_of_six w hw with ⟨s,hp,ho,he⟩
  refine ⟨Choice.complement s,(Choice.picked_complement s).mpr ho,
    (Choice.omitted_complement s).mpr hp,?_⟩
  have hprod := Choice.eval_mul_complement mod30Product s
  change Choice.eval mod30Product s = mod30Product.one at he
  rw [he,mod30Product.one_mul] at hprod
  exact hprod

theorem p2m_local_full_equals_proper_of_six (w : Word Code30) (hw : 6 ≤ length w) (u : Code30) :
    fullSupport mod30Product w u ↔ properSupport mod30Product w u := by
  constructor
  · intro h
    rcases (fullSupport_iff mod30Product w u).mp h with h | hu | hu
    · exact h
    · rw [hu]; exact proper_identity_of_six w hw
    · rw [hu]; exact proper_total_of_six w hw
  · rintro ⟨s,_,_,he⟩; exact ⟨s,he⟩









end S5
end Couret

theorem solution : ∀ (w : Couret.Word.{0} Couret.Code30),
  @LE.le.{0} Nat instLENat (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6)))
      (@Couret.S5.length Couret.Code30 w) →
    ∀ (u : Couret.Code30),
      Iff (@Couret.fullSupport.{0} Couret.Code30 Couret.mod30Product w u)
        (@Couret.properSupport.{0} Couret.Code30 Couret.mod30Product w u) := @_root_.Couret.S5.p2m_local_full_equals_proper_of_six

