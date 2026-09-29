-- Prove2me | solution 1 for lean_workbook_plus_7377
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:34:02.987291+00:00
-- url     : https://prove2.me/submissions/20110146-b1a9-460b-9ae5-a1c9000890a4

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {α : Type} [AddCommMonoid α] (f : α → α → α → α) (a b c : α) :
  f a b c + f a c b + f b a c + f b c a + f c a b + f c b a = (fun x y z => f x y z + f x z y + f y x z + f y z x + f z x y + f z y x) a b c := by
  norm_num
