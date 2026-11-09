-- Prove2me | Definitions.Def_Couret_BRIDGE01_A2_FixedModulusNoGain_7a86db44985c
-- name    : Couret_BRIDGE01_A2_FixedModulusNoGain_7a86db44985c
-- status  : Definition
-- author  : @alexcour
-- created : 2026-11-08T18:59:49.255759+00:00
-- url     : https://prove2.me/theorems/6f2dd1e7-d111-4e19-9db3-a078de7c718d
-- title:
--   Invertible real convolution on all eight unit coordinates
-- statement:
--   Let $U=(\mathbb Z/30)^\times$ and let $\mathbb R[U]$ have basis atoms $\delta_u$. The real kernel and its inverse are $$\tau=\delta_1+\delta_{11}+\delta_{29},\qquad\sigma=\tfrac13(\delta_1+\delta_{11}+\delta_{29}-2\delta_{19}).$$ Coefficientwise extension from $\mathbb Q[U]$ supplies the embedded identities $\tau\sigma=\sigma\tau=1$. The coefficient equivalence with $U\to\mathbb R$ induces a local norm $\|x\|=\max_{u\in U}|x_u|$ and local real normed-space structure. Multiplication by $\tau$ is packaged as a linear and continuous linear self-equivalence with inverse multiplication by $\sigma$. This is the full eight-coordinate interface for the later Big-O equivalence; the definitions do not assert an analytic improvement for scalar projections or changing moduli.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/d71ed2dafa9daa082f1a801b51d8a58abdb2c473/research/lean/CouretOaiBridge01/BRIDGE01_A2_FixedModulusNoGain.lean; source file SHA-256 d05751252a8be9b8319eca7acb46757defdefacd59a3142c705663fd5461cbac; proof-only compatibility repair; declaration headers and elaborated theorem types preserved

import Mathlib.Algebra.MonoidAlgebra.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.Asymptotics
import Mathlib.Data.ZMod.Units
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.Tactic.Abel
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Definitions.Def_Couret_BRIDGE01_A1_U30KernelInverse_5560f1024274
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.RingTheory.Finiteness.Finsupp
import Mathlib.Tactic.SplitIfs

/-!
# BRIDGE01 / A2: fixed-modulus no-gain on the full real coefficient vector

RESEARCH BRANCH ONLY — NO RH CLAIM — NO NOVELTY CLAIM.
The norm is the sup norm transported from all eight coefficient coordinates.
Completeness is used only for the real scalar field in Mathlib's continuity API.
-/

open Filter
open Asymptotics

namespace CouretOaiBridge01

noncomputable section

abbrev U30AlgR := MonoidAlgebra ℝ U30

def deltaR (u : U30) : U30AlgR := MonoidAlgebra.single u 1

def tauR : U30AlgR :=
  deltaR 1 + deltaR u11 + deltaR u29

def inverseNumeratorR : U30AlgR :=
  deltaR 1 + deltaR u11 + deltaR u29 - (deltaR u19 + deltaR u19)

def sigmaR : U30AlgR :=
  (1 / 3 : ℝ) • inverseNumeratorR

/-- The existing A1 certificate is extended coefficientwise from ℚ to ℝ. -/
def rationalToReal : U30Alg →+* U30AlgR :=
  MonoidAlgebra.mapRingHom U30 (Rat.castHom ℝ)

@[simp] theorem rationalToReal_tau : rationalToReal tau = tauR := by
  simp [rationalToReal, tau, tauR, delta, deltaR]

@[simp] theorem rationalToReal_sigma : rationalToReal sigma = sigmaR := by
  simp only [sigma, sigmaR, inverseNumerator, inverseNumeratorR,
    delta, deltaR, smul_sub, smul_add, MonoidAlgebra.smul_single]
  norm_num [rationalToReal, smul_eq_mul]





theorem tauR_mul_sigmaR : tauR * sigmaR = 1 := by
  simpa only [map_mul, rationalToReal_tau, rationalToReal_sigma, map_one] using
    congrArg rationalToReal tau_mul_sigma

theorem sigmaR_mul_tauR : sigmaR * tauR = 1 := by
  simpa only [map_mul, rationalToReal_tau, rationalToReal_sigma, map_one] using
    congrArg rationalToReal sigma_mul_tau





/-- Coefficient coordinates, identifying the real group algebra with eight real coordinates. -/
def coeffFunEquivR : U30AlgR ≃ₗ[ℝ] (U30 → ℝ) :=
  (MonoidAlgebra.coeffLinearEquiv ℝ).trans
    (Finsupp.linearEquivFunOnFinite ℝ ℝ U30)

/-- Sup norm on coefficient coordinates, transported to the group algebra. -/
local instance u30AlgRNormedAddCommGroup : NormedAddCommGroup U30AlgR :=
  NormedAddCommGroup.induced U30AlgR (U30 → ℝ)
    coeffFunEquivR.toLinearMap coeffFunEquivR.injective

local instance u30AlgRNormedSpace : NormedSpace ℝ U30AlgR :=
  NormedSpace.induced ℝ U30AlgR (U30 → ℝ) coeffFunEquivR.toLinearMap

/-- Left multiplication by the Couret kernel, with explicit inverse left multiplication by sigmaR. -/
def tauRMulLinearEquiv : U30AlgR ≃ₗ[ℝ] U30AlgR where
  toFun x := tauR * x
  invFun x := sigmaR * x
  map_add' x y := by simp [mul_add]
  map_smul' r x := mul_smul_comm _ _ _
  left_inv x := by
    change sigmaR * (tauR * x) = x
    rw [← mul_assoc, sigmaR_mul_tauR, one_mul]
  right_inv x := by
    change tauR * (sigmaR * x) = x
    rw [← mul_assoc, tauR_mul_sigmaR, one_mul]

/-- The finite-dimensional real realization of convolution by T_C as a continuous equivalence. -/
def tauRMulContinuousLinearEquiv : U30AlgR ≃L[ℝ] U30AlgR :=
  tauRMulLinearEquiv.toContinuousLinearEquiv





end

end CouretOaiBridge01


