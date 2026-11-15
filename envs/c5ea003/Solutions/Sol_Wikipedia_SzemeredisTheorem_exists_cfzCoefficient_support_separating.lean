-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.exists_cfzCoefficient_support_separating
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:09:56.117501+00:00
-- url     : https://prove2.me/submissions/1ec710b5-4008-417a-bedc-c1cc07644b46

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Independence of the Conlon--Fox--Zhao forms

The Goldston--Yıldırım linear-forms estimate requires the coefficient vectors
of distinct forms to be nonzero and pairwise non-proportional.  This file
records those facts over `ℤ` for the concrete CFZ family.
-/

namespace Wikipedia.SzemeredisTheorem









@[simp]
theorem cfzCoefficient_deleted {k : ℕ} (q : CFZFormIndex k) (b : Bool) :
    cfzCoefficient q (q.1, b) = 0 := by
  simp [cfzCoefficient]

@[simp]
theorem cfzCoefficient_selected {k : ℕ} (q : CFZFormIndex k)
    (i : {i : Fin k // i ≠ q.1}) :
    cfzCoefficient q (i.1, q.2 i) =
      (i.1 : ℤ) - (q.1 : ℤ) := by
  simp [cfzCoefficient, i.2]

theorem cfzCoefficient_unselected {k : ℕ} (q : CFZFormIndex k)
    (i : {i : Fin k // i ≠ q.1}) (b : Bool)
    (hb : b ≠ q.2 i) :
    cfzCoefficient q (i.1, b) = 0 := by
  simp [cfzCoefficient, i.2, hb]



theorem cfzCoefficient_selected_ne_zero {k : ℕ}
    (q : CFZFormIndex k) (i : {i : Fin k // i ≠ q.1}) :
    cfzCoefficient q (i.1, q.2 i) ≠ 0 := by
  rw [cfzCoefficient_selected]
  apply sub_ne_zero.mpr
  intro h
  apply i.2
  apply Fin.ext
  exact_mod_cast h











end Wikipedia.SzemeredisTheorem

end
/-!
# Independence of the Conlon--Fox--Zhao forms

The Goldston--Yıldırım linear-forms estimate requires the coefficient vectors
of distinct forms to be nonzero and pairwise non-proportional.  This file
records those facts over `ℤ` for the concrete CFZ family.
-/
open Wikipedia.SzemeredisTheorem

open Wikipedia.SzemeredisTheorem in
/-- Distinct CFZ forms have a doubled variable which occurs in the second
form but not in the first. -/
theorem solution {k : ℕ}
    (q r : CFZFormIndex k) (hqr : q ≠ r) :
    ∃ v : CFZVariable k,
      cfzCoefficient q v = 0 ∧ cfzCoefficient r v ≠ 0 := by
  rcases q with ⟨j, ω⟩
  rcases r with ⟨j', ω'⟩
  by_cases hj : j = j'
  · subst j'
    have hω : ω ≠ ω' := by
      intro h
      subst ω'
      exact hqr rfl
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hω
    refine ⟨(i.1, ω' i), ?_, cfzCoefficient_selected_ne_zero ⟨j, ω'⟩ i⟩
    exact cfzCoefficient_unselected ⟨j, ω⟩ i (ω' i) (Ne.symm hi)
  · let i : {i : Fin k // i ≠ j'} := ⟨j, hj⟩
    refine ⟨(j, ω' i), cfzCoefficient_deleted ⟨j, ω⟩ (ω' i), ?_⟩
    exact cfzCoefficient_selected_ne_zero ⟨j', ω'⟩ i
