-- Prove2me | solution 1 for Kourovka.MetabelianEnumeration.FourierMotzkin.Row.eval_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:00:54.974326+00:00
-- url     : https://prove2.me/submissions/973d7780-7a8e-4596-817e-b9a61baa1ed5

import Definitions.Def_Kourovka_Presentations_Presentations
import Definitions.Def_Kourovka_Polyhedral_FourierMotzkin

set_option autoImplicit true
open Kourovka Kourovka.MetabelianEnumeration Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Kourovka.MetabelianEnumeration.FourierMotzkin
namespace Row
theorem _root_.solution {n : ℕ} (r : Row (n + 1)) {K : Type*} [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] (t : K) (x : Fin n → K) :
    r.eval (Fin.cons t x) = (r.head : K) * t + r.tail.eval x := by
  simp [Row.eval, Row.head, Row.tail, Fin.sum_univ_succ, add_assoc]
end Row
end Kourovka.MetabelianEnumeration.FourierMotzkin
