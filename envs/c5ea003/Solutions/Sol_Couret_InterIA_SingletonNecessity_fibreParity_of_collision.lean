-- Prove2me | solution 1 for Couret.InterIA.SingletonNecessity.fibreParity_of_collision
-- status  : ACCEPTED   (prove)
-- author  : @alexcour
-- created : 2026-11-08T20:25:42.750362+00:00
-- url     : https://prove2.me/submissions/3042f39e-ec70-46db-a802-9480b585ca4d

import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Group.Pi.Basic
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Basic
import Mathlib.Data.List.Permutation
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Theorems.Thm_Couret_InterIA_SingletonNecessity_diagonal_parity_of_collision
import Theorems.Thm_Couret_InterIA_SingletonNecessity_nonzero_of_distinctLabels
import Theorems.Thm_Couret_InterIA_SingletonNecessity_sevenDistinct_injective
import Definitions.Def_Couret_ExtractionBasics_37ec1603f738
import Definitions.Def_Couret_SixDoublePairing_42d09f1cbb6a

set_option autoImplicit false
namespace Couret.InterIA.SingletonNecessity
open Finset Couret.InterIA.Parity
variable {G : Type*} [AddCommGroup G] [DecidableEq G]

theorem diagonal_four (a b c z : G) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    diagonalCount ({0,a,b,c} : Finset G) z =
      (if 0=z then 1 else 0) + (if a+a=z then 1 else 0) +
      (if b+b=z then 1 else 0) + (if c+c=z then 1 else 0) := by
  have h0 : (0:G) ∉ ({a,b,c}:Finset G) := by simp [Ne.symm ha,Ne.symm hb,Ne.symm hc]
  have h1 : a ∉ ({b,c}:Finset G) := by simp [hab,hac]
  have h2 : b ∉ ({c}:Finset G) := by simp [hbc]
  simp only [diagonalCount,Finset.sum_insert h0,Finset.sum_insert h1,
    Finset.sum_insert h2,Finset.sum_singleton,zero_add]
  omega



theorem diagonal_supportLeft (x : Fin 6 → G) (hd : SevenDistinct x) (z : G) :
    diagonalCount (supportLeft x) z =
      (if 0=z then 1 else 0) + (if x 0+x 0=z then 1 else 0) +
      (if x 1+x 1=z then 1 else 0) + (if x 2+x 2=z then 1 else 0) := by
  have hi := sevenDistinct_injective x hd
  exact diagonal_four _ _ _ _ (nonzero_of_distinctLabels x hd 0)
    (nonzero_of_distinctLabels x hd 1) (nonzero_of_distinctLabels x hd 2)
    (fun h => by have := hi h; contradiction)
    (fun h => by have := hi h; contradiction)
    (fun h => by have := hi h; contradiction)

theorem diagonal_supportRight (x : Fin 6 → G) (hd : SevenDistinct x) (z : G) :
    diagonalCount (supportRight x) z =
      (if 0=z then 1 else 0) + (if x 3+x 3=z then 1 else 0) +
      (if x 4+x 4=z then 1 else 0) + (if x 5+x 5=z then 1 else 0) := by
  have hi := sevenDistinct_injective x hd
  exact diagonal_four _ _ _ _ (nonzero_of_distinctLabels x hd 3)
    (nonzero_of_distinctLabels x hd 4) (nonzero_of_distinctLabels x hd 5)
    (fun h => by have := hi h; contradiction)
    (fun h => by have := hi h; contradiction)
    (fun h => by have := hi h; contradiction)





theorem p2m_local_fibreParity_of_collision (x : Fin 6 → G) (hd : SevenDistinct x)
    (hs : ∀ z, orderedSquare (supportLeft x) z=orderedSquare (supportRight x) z) :
    FibreParity (fun i => x i+x i) := by
  intro z
  have h := diagonal_parity_of_collision _ _ hs z
  rw [diagonal_supportLeft x hd,diagonal_supportRight x hd] at h
  change ((if x 0+x 0=z then 1 else 0)+(if x 1+x 1=z then 1 else 0)+
    (if x 2+x 2=z then 1 else 0):ℕ)%2 =
    ((if x 3+x 3=z then 1 else 0)+(if x 4+x 4=z then 1 else 0)+
    (if x 5+x 5=z then 1 else 0):ℕ)%2
  omega

end Couret.InterIA.SingletonNecessity

universe p2m_u_0
theorem solution : ∀ {G : Type p2m_u_0} [inst : AddCommGroup.{p2m_u_0} G] [inst_1 : DecidableEq.{p2m_u_0 + 1} G]
  (x : Fin (@OfNat.ofNat.{0} Nat (nat_lit 6) (instOfNatNat (nat_lit 6))) → G),
  @Couret.InterIA.SingletonNecessity.SevenDistinct.{p2m_u_0} G inst x →
    (∀ (z : G),
        @Eq.{1} Nat
          (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1
            (@Couret.InterIA.SingletonNecessity.supportLeft.{p2m_u_0} G inst inst_1 x) z)
          (@Couret.InterIA.Parity.orderedSquare.{p2m_u_0} G inst inst_1
            (@Couret.InterIA.SingletonNecessity.supportRight.{p2m_u_0} G inst inst_1 x) z)) →
      @Couret.InterIA.SingletonNecessity.FibreParity.{p2m_u_0} G inst_1 fun i =>
        @HAdd.hAdd.{p2m_u_0, p2m_u_0, p2m_u_0} G G G
          (@instHAdd.{p2m_u_0} G
            (@AddCommMagma.toAdd.{p2m_u_0} G
              (@AddCommSemigroup.toAddCommMagma.{p2m_u_0} G
                (@AddCommMonoid.toAddCommSemigroup.{p2m_u_0} G (@AddCommGroup.toAddCommMonoid.{p2m_u_0} G inst)))))
          (x i) (x i) := @_root_.Couret.InterIA.SingletonNecessity.p2m_local_fibreParity_of_collision

