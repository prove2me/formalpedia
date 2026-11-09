-- Prove2me | solution 1 for Couret.Choice.eval_mul_complement
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T19:40:42.129904+00:00
-- url     : https://prove2.me/submissions/c5741004-dd32-4b4a-8197-3f3101769c36

import Definitions.Def_Couret_SupportSemantics_a8ae2832b450
import Std
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































theorem p2m_local_eval_mul_complement (M : CMonoid α) {w : Word α} (s : Choice w) :
    M.mul (eval M s) (eval M (complement s)) = total M w := by
  induction s with
  | empty => exact M.mul_one M.one
  | skip s g ih =>
    calc
      M.mul (eval M s) (M.mul (eval M (complement s)) g) =
          M.mul (M.mul (eval M s) (eval M (complement s))) g := (M.assoc _ _ _).symm
      _ = M.mul (total M _) g := congrArg (fun x => M.mul x g) ih
  | take s g ih =>
    calc
      M.mul (M.mul (eval M s) g) (eval M (complement s)) =
          M.mul (eval M s) (M.mul g (eval M (complement s))) := M.assoc _ _ _
      _ = M.mul (eval M s) (M.mul (eval M (complement s)) g) :=
          congrArg (fun x => M.mul (eval M s) x) (M.comm _ _)
      _ = M.mul (M.mul (eval M s) (eval M (complement s))) g := (M.assoc _ _ _).symm
      _ = M.mul (total M _) g := congrArg (fun x => M.mul x g) ih

end Choice







































/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret


universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} (M : Couret.CMonoid.{p2m_u_0} α) {w : Couret.Word.{p2m_u_0} α} (s : @Couret.Choice.{p2m_u_0} α w),
  @Eq.{p2m_u_0 + 1} α
    (@Couret.CMonoid.mul.{p2m_u_0} α M (@Couret.Choice.eval.{p2m_u_0} α M w s)
      (@Couret.Choice.eval.{p2m_u_0} α M w (@Couret.Choice.complement.{p2m_u_0} α w s)))
    (@Couret.total.{p2m_u_0} α M w) := @_root_.Couret.Choice.p2m_local_eval_mul_complement

