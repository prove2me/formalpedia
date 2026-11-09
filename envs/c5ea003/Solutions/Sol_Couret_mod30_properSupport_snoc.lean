-- Prove2me | solution 1 for Couret.mod30_properSupport_snoc
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:00:02.560024+00:00
-- url     : https://prove2.me/submissions/ac2089ba-456d-4bc8-b0b8-8735da2c051c

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
import Theorems.Thm_Couret_properSupport_snoc
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

































end Choice







































/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/
























theorem p2m_local_mod30_properSupport_snoc (w : Word Code30) (hw : w.nonempty)
    (g u : Code30) :
    properSupport mod30Product (.snoc w g) u ↔
      properSupport mod30Product w u ∨
      (∃ v, properSupport mod30Product w v ∧ mul30 g v = u) ∨
      u = total mod30Product w ∨ u = g :=
  properSupport_snoc mod30Product w hw g u

end Couret


theorem solution : ∀ (w : Couret.Word.{0} Couret.Code30),
  @Couret.Word.nonempty.{0} Couret.Code30 w →
    ∀ (g u : Couret.Code30),
      Iff (@Couret.properSupport.{0} Couret.Code30 Couret.mod30Product (@Couret.Word.snoc.{0} Couret.Code30 w g) u)
        (Or (@Couret.properSupport.{0} Couret.Code30 Couret.mod30Product w u)
          (Or
            (@Exists.{1} Couret.Code30 fun v =>
              And (@Couret.properSupport.{0} Couret.Code30 Couret.mod30Product w v)
                (@Eq.{1} Couret.Code30 (Couret.mul30 g v) u))
            (Or (@Eq.{1} Couret.Code30 u (@Couret.total.{0} Couret.Code30 Couret.mod30Product w))
              (@Eq.{1} Couret.Code30 u g)))) := @_root_.Couret.p2m_local_mod30_properSupport_snoc

