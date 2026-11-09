-- Prove2me | solution 1 for Couret.Choice.omitted_complement
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:24:58.023635+00:00
-- url     : https://prove2.me/submissions/7ba4e48c-94a1-431d-975e-95557ba391b6

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





























theorem p2m_local_omitted_complement {w : Word α} (s : Choice w) :
    omitted (complement s) ↔ picked s := by
  induction s with
  | empty => rfl
  | skip s g ih => exact ih
  | take s g ih => exact Iff.rfl



end Choice







































/- Concrete eight-element alphabet, with the same coordinates as the Python
   verifier: 1,7,19,13 and 11,17,29,23. These finite laws use kernel `decide`,
   not native_decide. -/


























end Couret


universe p2m_u_0
theorem solution : ∀ {α : Type p2m_u_0} {w : Couret.Word.{p2m_u_0} α} (s : @Couret.Choice.{p2m_u_0} α w),
  Iff (@Couret.Choice.omitted.{p2m_u_0} α w (@Couret.Choice.complement.{p2m_u_0} α w s))
    (@Couret.Choice.picked.{p2m_u_0} α w s) := @_root_.Couret.Choice.p2m_local_omitted_complement

