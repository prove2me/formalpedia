-- Prove2me | solution 1 for MomentAngleSurgery.cokernel_equiv_blocks
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T11:12:50.886535+00:00
-- url     : https://prove2.me/submissions/268104f0-cec7-419f-9e28-57187ddad512

import Definitions.Def_MomentAngle_surgery_blocks
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Complete algebraic cokernel computation for the zero-surgery block matrix.
The geometric connection to singular homology is a separate open theorem. -/

namespace SurgeryCokernelAnalysis

open MomentAngleSurgery

private def reduction (n k : ℕ) : Generators k →+
    ((Fin k → ℤ) × (Fin k → ZMod n) × (Fin k → ZMod n)) where
  toFun x := (x.1, (fun i => (x.2.1 i : ZMod n)), (fun i => (x.2.2 i : ZMod n)))
  map_zero' := by ext i <;> simp
  map_add' x y := by ext i <;> simp

private theorem reduction_surjective (n k : ℕ) : Function.Surjective (reduction n k) := by
  intro v
  choose b hb using fun i : Fin k => ZMod.intCast_surjective (v.2.1 i)
  choose c hc using fun i : Fin k => ZMod.intCast_surjective (v.2.2 i)
  refine ⟨(v.1, b, c), ?_⟩
  ext i <;> simp [reduction, hb, hc]

private theorem ker_eq_range (n k : ℕ) :
    (reduction n k).ker = (linkingMap n k).range := by
  ext x
  change reduction n k x = 0 ↔ ∃ y, linkingMap n k y = x
  constructor
  · intro h
    have ha : x.1 = 0 := congrArg Prod.fst h
    have hb : ∀ i : Fin k, (n : ℤ) ∣ x.2.1 i := by
      intro i
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      exact congrArg (fun z => z.2.1 i) h
    have hc : ∀ i : Fin k, (n : ℤ) ∣ x.2.2 i := by
      intro i
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp
      exact congrArg (fun z => z.2.2 i) h
    choose b hb' using hb
    choose c hc' using hc
    refine ⟨(0, c, b), ?_⟩
    apply Prod.ext ha.symm
    apply Prod.ext
    · exact funext (fun i => (hb' i).symm)
    · exact funext (fun i => (hc' i).symm)
  · rintro ⟨y, rfl⟩
    ext i <;> simp [reduction, linkingMap]

noncomputable def cokernelEquiv (n k : ℕ) : Cokernel n k ≃+
    ((Fin k → ℤ) × (Fin k → ZMod n) × (Fin k → ZMod n)) :=
  (QuotientAddGroup.quotientAddEquivOfEq (ker_eq_range n k).symm).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective (reduction n k)
      (reduction_surjective n k))

end SurgeryCokernelAnalysis

open MomentAngleSurgery

theorem solution (n k : ℕ) : Nonempty (Cokernel n k ≃+
    ((Fin k → ℤ) × (Fin k → ZMod n) × (Fin k → ZMod n))) :=
  ⟨SurgeryCokernelAnalysis.cokernelEquiv n k⟩

#print axioms solution
