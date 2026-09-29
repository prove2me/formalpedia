-- Prove2me | solution 1 for lean_workbook_plus_19088
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:49:36.71705+00:00
-- url     : https://prove2.me/submissions/4189ed28-3488-4b56-8d40-45519ea1890c

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Data.Nat.Choose.Lucas

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution : (Nat.choose 2007 91) % 91 = 5 := by
  letI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  letI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have h7 : Nat.choose 2007 91 ≡ 5 [MOD 7] := by
    have h := Choose.choose_modEq_prod_range_choose_nat (p:=7) (n:=2007) (k:=91)
      (a:=4) (by norm_num) (by norm_num)
    exact h.trans (by norm_num [Finset.prod_range_succ,Nat.choose,Nat.ModEq])
  have h13 : Nat.choose 2007 91 ≡ 5 [MOD 13] := by
    have h := Choose.choose_modEq_prod_range_choose_nat (p:=13) (n:=2007) (k:=91)
      (a:=3) (by norm_num) (by norm_num)
    exact h.trans (by norm_num [Finset.prod_range_succ,Nat.choose,Nat.ModEq])
  have h91 : Nat.choose 2007 91 ≡ 5 [MOD 91] :=
    (Nat.modEq_and_modEq_iff_modEq_mul (a:=Nat.choose 2007 91) (b:=5)
      (by decide : Nat.Coprime 7 13)).mp ⟨h7,h13⟩
  exact h91
