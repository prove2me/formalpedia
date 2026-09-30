-- Prove2me | solution 1 for Hirsch.q28_quotient_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T23:07:58.519907+00:00
-- url     : https://prove2.me/submissions/aef9063a-eff0-4183-8f1b-086e155ad6c2

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert

open scoped RealInnerProductSpace
open Set Classical Hirsch Matrix

set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

theorem fourAll_true : fourAll = true := rfl

lemma of20_val (o : Fin 20) : of20 o.val = o :=
  Fin.ext (Nat.mod_eq_of_lt o.isLt)

lemma of16_val (s : Fin 16) : of16 s.val = s :=
  Fin.ext (Nat.mod_eq_of_lt s.isLt)

lemma of14_val (s : Fin 14) : of14 s.val = s :=
  Fin.ext (Nat.mod_eq_of_lt s.isLt)

theorem four_actives_in_quotient :
    ∀ (o1 o2 : Fin 20) (s : Fin 16),
      4 ≤ commonActiveCard o1 o2 s →
      o1 = o2 ∨ QuotientAdj o1 o2 := by
  intro o1 o2 s hcard
  have h := fourAll_true
  simp [fourAll, List.all_eq_true, List.mem_range] at h
  have hok : fourOk o1.val o2.val s.val = true :=
    h o1.val o1.isLt o2.val o2.isLt s.val s.isLt
  have hprop := of_decide_eq_true (by simpa [fourOk] using hok)
  rcases hprop with hlt | heq | hadj | hadj
  · have : cardAt (o1.val * 320 + o2.val * 16 + s.val) < 4 := hlt
    simp [commonActiveCard] at hcard
    omega
  · exact Or.inl (Fin.ext heq)
  · exact Or.inr (Or.inl hadj)
  · exact Or.inr (Or.inr hadj)

theorem gapAll_true : gapAll = true := rfl

theorem common_active_of_level_gap :
    ∀ (o1 o2 : Fin 20) (s : Fin 16),
      1 < max (orbitLevel o1) (orbitLevel o2) - min (orbitLevel o1) (orbitLevel o2) →
      commonActiveCard o1 o2 s ≤ 3 := by
  intro o1 o2 s hgap
  have h := gapAll_true
  simp [gapAll, List.all_eq_true, List.mem_range] at h
  have hok : gapOk o1.val o2.val s.val = true :=
    h o1.val o1.isLt o2.val o2.isLt s.val s.isLt
  have hprop := of_decide_eq_true (by simpa [gapOk] using hok)
  rcases hprop with hle | hcard
  · have ho1 := of20_val o1
    have ho2 := of20_val o2
    simp [ho1, ho2] at hle
    omega
  · simpa [commonActiveCard] using hcard

theorem orbitLevel_step :
    ∀ i j : Fin 20, QuotientAdj i j → orbitLevel j ≤ orbitLevel i + 1 := by
  decide

theorem mask_bit :
    ∀ (o : Fin 20) (s : Fin 16) (i : Fin 28),
      (tightMask o s).testBit i.val = true ↔
        intDotFlip o s i = orbitDen o := by
  decide

theorem solution :
    (∀ o1 o2 : Fin 20, ∀ s : Fin 16,
      4 ≤ commonActiveCard o1 o2 s → o1 = o2 ∨ QuotientAdj o1 o2) ∧
    (∀ o1 o2 : Fin 20, ∀ s : Fin 16,
      1 < max (orbitLevel o1) (orbitLevel o2) -
            min (orbitLevel o1) (orbitLevel o2) →
        commonActiveCard o1 o2 s ≤ 3) ∧
    (∀ i j : Fin 20, QuotientAdj i j → orbitLevel j ≤ orbitLevel i + 1) ∧
    (∀ o : Fin 20, ∀ s : Fin 16, ∀ i : Fin 28,
      (tightMask o s).testBit i.val = true ↔
        intDotFlip o s i = orbitDen o) :=
  ⟨four_actives_in_quotient, common_active_of_level_gap, orbitLevel_step, mask_bit⟩
