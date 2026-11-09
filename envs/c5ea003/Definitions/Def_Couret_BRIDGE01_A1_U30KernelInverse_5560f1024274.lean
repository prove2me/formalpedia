-- Prove2me | Definitions.Def_Couret_BRIDGE01_A1_U30KernelInverse_5560f1024274
-- name    : Couret_BRIDGE01_A1_U30KernelInverse_5560f1024274
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:12.717635+00:00
-- url     : https://prove2.me/theorems/0c50fedd-a5fa-41c3-a666-ddca6137330e
-- title:
--   Rational group-algebra kernel on units modulo thirty
-- statement:
--   Defines U30=(ZMod 30)ˣ and its rational monoid algebra, the explicit units 11,19,29, and delta(u), the basis element at u with coefficient one. The kernel tau is delta(1)+delta(11)+delta(29); inverseNumerator is that sum minus twice delta(19), and sigma is one third of inverseNumerator. The bundle also contains delta_one, the identity delta(1)=1 in the group algebra, the elementary unit multiplication identities and the resulting left and right inverse identities for tau and sigma. These are finite algebraic objects on this fixed modulus.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/BRIDGE01_A1_U30KernelInverse.lean; source file SHA-256 ca0ed4d030d67c53ca6a07164314c25550709108f4005bb62315f8c43a7f328a

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

abbrev U30 := (ZMod 30)ˣ
abbrev U30Alg := MonoidAlgebra ℚ U30



def u11 : U30 := ZMod.unitOfCoprime 11 (by decide)
def u19 : U30 := ZMod.unitOfCoprime 19 (by decide)
def u29 : U30 := ZMod.unitOfCoprime 29 (by decide)

def delta (u : U30) : U30Alg := MonoidAlgebra.single u 1

def tau : U30Alg :=
  delta 1 + delta u11 + delta u29

def inverseNumerator : U30Alg :=
  delta 1 + delta u11 + delta u29 - (delta u19 + delta u19)

def sigma : U30Alg :=
  (1 / 3 : ℚ) • inverseNumerator

theorem u11_sq : u11 * u11 = 1 := by decide

theorem u29_sq : u29 * u29 = 1 := by decide

theorem u11_mul_u29 : u11 * u29 = u19 := by decide
theorem u29_mul_u11 : u29 * u11 = u19 := by decide
theorem u11_mul_u19 : u11 * u19 = u29 := by decide

theorem u29_mul_u19 : u29 * u19 = u11 := by decide


@[simp] theorem delta_one : delta 1 = 1 := rfl

@[simp] theorem delta_mul (u v : U30) :
    delta u * delta v = delta (u * v) := by
  simp [delta, MonoidAlgebra.single_mul_single]

private theorem kernel_product :
    tau * inverseNumerator = delta 1 + delta 1 + delta 1 := by
  simp only [tau, inverseNumerator, mul_sub, mul_add, add_mul, delta_mul]
  simp only [one_mul, mul_one, u11_sq, u29_sq, u11_mul_u29, u29_mul_u11,
    u11_mul_u19, u29_mul_u19]
  abel

theorem tau_mul_sigma : tau * sigma = 1 := by
  rw [sigma, mul_smul_comm, kernel_product]
  have hthree : delta 1 + delta 1 + delta 1 = 3 • delta 1 := by
    abel
  rw [hthree]
  rw [← Nat.cast_smul_eq_nsmul ℚ]
  rw [smul_smul]
  norm_num

theorem sigma_mul_tau : sigma * tau = 1 := by
  rw [mul_comm]
  exact tau_mul_sigma

end

end CouretOaiBridge01


