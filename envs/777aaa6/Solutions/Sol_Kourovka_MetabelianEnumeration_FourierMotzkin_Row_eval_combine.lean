-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FourierMotzkin.Row.eval_combine
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:55.778893+00:00
-- url     : https://prove2.me/submissions/415a0b4e-8640-4524-9416-69a39a352208

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Row
theorem _root_.solution {n : ℕ} (l u : Row (n + 1)) {K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] (x : Fin n → K) :
    (l.combine u).eval x = (u.head : K) * l.tail.eval x -
      (l.head : K) * u.tail.eval x := by
  simp only [Row.eval, Row.combine, Row.tail, Rat.cast_sub, Rat.cast_mul]
  simp_rw [sub_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring
end Row
end Kourovka.MetabelianEnumeration.FourierMotzkin
