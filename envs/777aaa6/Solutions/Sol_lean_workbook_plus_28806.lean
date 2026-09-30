-- Prove2me | solution 1 for lean_workbook_plus_28806
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T03:21:50.808887+00:00
-- url     : https://prove2.me/submissions/972ced5b-b723-4867-9fca-1d581f3dc95f

import Mathlib.GroupTheory.OrderOfElement

theorem solution {G : Type*} [Group G] {g h : G}
    (hg : IsOfFinOrder g) (hh : IsOfFinOrder h) (hgh : Commute g h)
    (hmn : Nat.Coprime (orderOf g) (orderOf h)) :
    orderOf (g * h) = (orderOf g) * (orderOf h) := by
  exact hgh.orderOf_mul_eq_mul_orderOf_of_coprime hmn

#print axioms solution
