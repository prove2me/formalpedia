-- Prove2me | solution 1 for Fpy.DigitBound.Con.dep
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T06:12:54.822241+00:00
-- url     : https://prove2.me/submissions/5f77f41b-8529-476a-a855-7c51880abebf

import Definitions.Def_Fpy_FormatInference_Defs
import Definitions.Def_Fpy_Ops
import Mathlib.Order.WithBotTop
import Definitions.Def_Fpy_DigitBound_Defs
import Theorems.Thm_Fpy_DigitBound_Term_eval_congr

set_option autoImplicit true
open Fpy Fpy.DigitBound
open Mpfx
namespace Fpy.DigitBound
namespace Con
theorem _root_.solution (c : Con) {ι ι' : Asgn} (h : ∀ x ≤ c.head, ι x = ι' x) (hP : c.P ι) :
    c.P ι' := fun a ha => by
  have h' : ∀ x < c.head + 1, ι x = ι' x := fun x hx => h x (Nat.lt_succ_iff.mp hx)
  have hb := c.below a ha
  have := hP a ha
  rwa [Atom.Holds, Term.eval_congr h' hb.1, Term.eval_congr h' hb.2] at this
end Con
end Fpy.DigitBound
