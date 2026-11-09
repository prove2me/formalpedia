-- Prove2me | solution 1 for CouretOaiBridge01.u19_mul_u29
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T21:02:45.43987+00:00
-- url     : https://prove2.me/submissions/22d53aa4-74ec-4fa5-9ee4-9cd03b360c7c

import Definitions.Def_Couret_BRIDGE01_A1_U30KernelInverse_5560f1024274
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum

/-!
# BRIDGE01 / A1: exact inverse in the rational group algebra of U(30)

RESEARCH BRANCH ONLY — NO RH CLAIM — NO NOVELTY CLAIM.
The finite identities use kernel `decide`. A2 reuses this certificate.
-/

namespace CouretOaiBridge01

noncomputable section



























theorem p2m_local_u19_mul_u29 : u19 * u29 = u11 := by decide











end

end CouretOaiBridge01

theorem solution : @Eq.{1} CouretOaiBridge01.U30
  (@HMul.hMul.{0, 0, 0} CouretOaiBridge01.U30 CouretOaiBridge01.U30 CouretOaiBridge01.U30
    (@instHMul.{0} CouretOaiBridge01.U30
      (@Units.instMul.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
        (@Semiring.toMonoid.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
          (@CommSemiring.toSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
            (@CommRing.toCommSemiring.{0} (ZMod (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30))))
              (ZMod.commRing (@OfNat.ofNat.{0} Nat (nat_lit 30) (instOfNatNat (nat_lit 30)))))))))
    CouretOaiBridge01.u19 CouretOaiBridge01.u29)
  CouretOaiBridge01.u11 := @_root_.CouretOaiBridge01.p2m_local_u19_mul_u29

