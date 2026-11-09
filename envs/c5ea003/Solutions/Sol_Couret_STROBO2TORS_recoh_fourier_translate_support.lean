-- Prove2me | solution 1 for Couret.STROBO2TORS.recoh_fourier_translate_support
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:54:13.633269+00:00
-- url     : https://prove2.me/submissions/0743a2e0-b228-43e4-8f33-2a57b9fdda50

import Aesop
import Definitions.Def_Couret_RecohFourierCovarianceBridge_d0f4471a4239
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Tauto
import Definitions.Def_Couret_Strobo2TorsCore_3589e2e5b464
import Mathlib.Algebra.Group.AddChar
import Mathlib.Data.Complex.Basic

set_option autoImplicit false

/-!
RECOH Fourier covariance bridge — retained copy of the previously certified module.
The existence of a separating character for arbitrary distinct supports remains
an open formalization obligation; do not confuse nonvanishing with separation.
-/

namespace Couret.STROBO2TORS

variable {G : Type*} [AddCommGroup G]







/-- Pointwise shifts of Fourier summands obey character covariance. -/
theorem recoh_fourier_sum_shift (chi : AddChar G ℂ)
    (S : Finset G) (u : G) :
    S.sum (fun x => chi (x + u)) = recohFourierSum chi S * chi u := by
  calc
    S.sum (fun x => chi (x + u)) =
        S.sum (fun x => chi x * chi u) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact chi.map_add_eq_mul x u
    _ = recohFourierSum chi S * chi u := by
          simp [recohFourierSum, Finset.sum_mul]



/-- Fourier covariance under translation of the actual support. -/
theorem p2m_local_recoh_fourier_translate_support [DecidableEq G]
    (chi : AddChar G ℂ) (S : Finset G) (u : G) :
    recohFourierSum chi (translateSupport S u) =
      recohFourierSum chi S * chi u := by
  unfold recohFourierSum translateSupport
  rw [Finset.sum_image (by
    intro a ha b hb hab
    exact add_right_cancel hab)]
  exact recoh_fourier_sum_shift chi S u


end Couret.STROBO2TORS

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (chi :
    @AddChar.{p2m_u_0, 0} G
      (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
        (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
      Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
  (S : Finset.{p2m_u_0} G) (u : G),
  @Eq.{1} Complex
    (@Couret.STROBO2TORS.recohFourierSum.{p2m_u_0} G inst chi
      (@Couret.STROBO2TORS.translateSupport.{p2m_u_0} G inst inst_1 S u))
    (@HMul.hMul.{0, 0, 0} Complex Complex Complex (@instHMul.{0} Complex Complex.instMul)
      (@Couret.STROBO2TORS.recohFourierSum.{p2m_u_0} G inst chi S)
      (@DFunLike.coe.{p2m_u_0 + 1, p2m_u_0 + 1, 1}
        (@AddChar.{p2m_u_0, 0} G
          (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
          Complex (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
        G (fun x => Complex)
        (@AddChar.instFunLike.{p2m_u_0, 0} G Complex
          (@SubNegMonoid.toAddMonoid.{p2m_u_0} G
            (@AddGroup.toSubNegMonoid.{p2m_u_0} G (@AddCommGroup.toAddGroup.{p2m_u_0} G inst)))
          (@Semiring.toMonoid.{0} Complex Complex.instSemiring))
        chi u)) := @_root_.Couret.STROBO2TORS.p2m_local_recoh_fourier_translate_support

