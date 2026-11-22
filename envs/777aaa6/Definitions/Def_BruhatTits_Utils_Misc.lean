-- Prove2me | Definitions.Def_BruhatTits_Utils_Misc
-- name    : BruhatTits_Utils_Misc
-- status  : Definition
-- author  : @marwahaha
-- created : 2026-11-21T09:40:28.883947+00:00
-- url     : https://prove2.me/theorems/98458b2f-c53e-4c03-afde-2e905d5343be
-- title:
--   Misc
-- statement:
--   Definitions and structural lemmas for Misc, from Judith Ludwig, Christian Merten, and contributors's pinned The Bruhat–Tits tree development. This module supplies the shared objects used by its theorem proofs.
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Misc.lean

import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Tactic
import Mathlib.GroupTheory.DoubleCoset
set_option autoImplicit false
namespace P2MCompatibility
instance (priority := 2000) legacyPNatCast (n : ℕ) [NeZero n] : Coe ℕ+ (Fin n) := ⟨fun x => Fin.ofNat n x.val⟩
instance legacyNatCast (n : ℕ) [NeZero n] : Coe ℕ (Fin n) := ⟨fun x => Fin.ofNat n x⟩
instance legacyFinCast (m n : ℕ) [NeZero n] (x : Fin m) : CoeDep (Fin m) x (Fin n) := ⟨Fin.ofNat n x.val⟩
instance legacyNatToFin (n : ℕ) : Coe ℕ (Fin (n + 1)) := ⟨fun x => Fin.ofNat (n + 1) x⟩
instance legacyFinToFin (n : ℕ) : Coe (Fin n) (Fin (n + 1)) := ⟨fun x => Fin.ofNat (n + 1) x.val⟩
example (n : ℕ) (x : Fin n) : (x : Fin (n + 1)) = x.castSucc := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (Nat.lt_trans x.isLt (Nat.lt_succ_self n))
example (n : ℕ) : ((n : ℕ) : Fin (n + 1)) = Fin.last n := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (Nat.lt_succ_self n)
example (l : ℕ+) : (l : Fin ((l : ℕ) + 1)) = Fin.last (l : ℕ) := by
  apply Fin.ext
  exact Nat.mod_eq_of_lt (Nat.lt_succ_self _)
end P2MCompatibility
namespace Doset
open scoped Pointwise
abbrev doset {α : Type*} [Mul α] (a : α) (s t : Set α) : Set α :=
  DoubleCoset.doubleCoset a s t
example {α : Type*} [Mul α] (a : α) (s t : Set α) : doset a s t = s * {a} * t := rfl
end Doset
variable {α β γ : Type*}
variable {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
@[simp]
lemma Matrix.GeneralLinearGroup.toLinear_symm_ofLinearEquiv_apply
    {ι : Type*} [DecidableEq ι] [Fintype ι] {R : Type*} [CommRing R]
    (e : (ι → R) ≃ₗ[R] ι → R) (i j : ι) :
    Matrix.GeneralLinearGroup.toLin.symm (LinearMap.GeneralLinearGroup.ofLinearEquiv e) i j =
      e (Pi.single j 1) i :=
  rfl
namespace Finset
variable {ι α β : Type*} [CommGroupWithZero β]
end Finset
section
variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] [IsNoetherianRing R]
end
@[simps]
def Fin.succ_equiv_unit (n : ℕ) : Fin (n + 1) ≃ Fin n ⊕ Unit where
  toFun j := if h : (j : ℕ) < n then Sum.inl ⟨j, h⟩ else Sum.inr ()
  invFun := Sum.elim (fun j ↦ j) (fun _ ↦ n)
  left_inv j := by
    simp only
    split_ifs with h
    · simp
    · ext
      simp_all only [not_lt, Sum.elim_inr, Fin.ofNat, Nat.mod_succ]
      apply le_antisymm h (is_le j)
  right_inv
    | Sum.inl i => by
        simp only [Sum.elim_inl, Fin.ofNat]
        split_ifs with h
        · rw [Sum.inl.injEq]
          ext
          simp only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one]
          exact Nat.lt_add_right 1 i.isLt
        · have hlt : i < n + 1 := Nat.lt_add_right 1 i.isLt
          simp_all only [not_lt]
          rw [Nat.mod_eq_of_lt hlt] at h
          omega
    | Sum.inr () => by simp


