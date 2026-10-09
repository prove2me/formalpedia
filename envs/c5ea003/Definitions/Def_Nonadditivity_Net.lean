-- Prove2me | Definitions.Def_Nonadditivity_Net
-- name    : Nonadditivity_Net
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:32:55.212897+00:00
-- url     : https://prove2.me/theorems/a3510a84-aa04-4187-a0f1-ae93359572eb
-- title:
--   Finite sphere nets and matrix-norm certificates
-- statement:
--   Compactness of the unit sphere in a finite-dimensional real normed space provides finite unit-vector tests at every positive radius. If a continuous linear map is bounded by $B$ on a radius-$\delta$ net with $0\le\delta<1$, its operator norm is at most $B/(1-\delta)$. The interface specializes the radius to a prescribed multiplicative tolerance and defines the free norm and Collins–Youn constants with their positivity and purity-factor estimates. These certificates convert finite tests into uniform matrix norm bounds.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/Net.lean#L36-L363

import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/










/-!
# Finite observable tests and the uniform norm certificate

The traceless Hermitian matrices with Hilbert--Schmidt norm form a real
finite dimensional normed space.  The results below apply to this space
without replacing a linear operator by a table of scalar bounds.

The external Collins--Youn and random-matrix convergence theorems are
represented by explicit bound and convergence hypotheses. They are not
declared as axioms or treated as results proved by this file.
-/

namespace Nonadditivity

open Metric

section FiniteNet

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A finite set of tests approximating every unit vector. -/
def UnitSphereNet (tests : Finset E) (δ : ℝ) : Prop :=
  ∀ x : E, ‖x‖ = 1 → ∃ y ∈ tests, dist x y ≤ δ

/-- Compactness supplies finite unit-vector tests independently of any map. -/
theorem exists_unitSphereNet [FiniteDimensional ℝ E] {δ : ℝ} (hδ : 0 < δ) :
    ∃ tests : Finset E,
      (∀ y ∈ tests, ‖y‖ = 1) ∧ UnitSphereNet tests δ := by
  classical
  obtain ⟨s, hsphere, hs, hcover⟩ := (isCompact_sphere (0 : E) 1).finite_cover_balls hδ
  refine ⟨hs.toFinset, ?_, ?_⟩
  · intro y hy
    have := hsphere (hs.mem_toFinset.mp hy)
    simpa [Metric.mem_sphere, dist_zero_right] using this
  · intro x hx
    have hxmem : x ∈ sphere (0 : E) 1 := by simpa [Metric.mem_sphere, dist_zero_right]
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (hcover hxmem)
    exact ⟨y, hs.mem_toFinset.mpr hy, le_of_lt hxy⟩

/-- The central net argument: finite test bounds control the actual operator norm.
The estimate is valid in arbitrary real normed spaces once a net is given. -/
theorem opNorm_le_of_unitSphereNet (T : E →L[ℝ] F) {tests : Finset E} {δ B : ℝ}
    (hδnonneg : 0 ≤ δ) (hδ : δ < 1) (hB : 0 ≤ B)
    (hnet : UnitSphereNet tests δ) (htests : ∀ y ∈ tests, ‖T y‖ ≤ B) :
    ‖T‖ ≤ B / (1 - δ) := by
  have hunit : ‖T‖ ≤ B + δ * ‖T‖ := by
    apply ContinuousLinearMap.opNorm_le_of_unit_norm
      (add_nonneg hB (mul_nonneg hδnonneg (norm_nonneg T)))
    intro x hx
    obtain ⟨y, hy, hxy⟩ := hnet x hx
    calc
      ‖T x‖ = ‖T y + T (x - y)‖ := by rw [map_sub]; congr 1; abel
      _ ≤ ‖T y‖ + ‖T (x - y)‖ := norm_add_le _ _
      _ ≤ B + ‖T‖ * ‖x - y‖ := add_le_add (htests y hy) (T.le_opNorm _)
      _ ≤ B + ‖T‖ * δ := add_le_add (le_refl B)
        (mul_le_mul_of_nonneg_left (by simpa [dist_eq_norm] using hxy) (norm_nonneg T))
      _ = B + δ * ‖T‖ := by ring
  apply (le_div_iff₀ (by linarith : 0 < 1 - δ)).mpr
  nlinarith

/-- Homogeneous form of the finite-test certificate. -/
theorem norm_apply_le_of_unitSphereNet (T : E →L[ℝ] F) {tests : Finset E} {δ B : ℝ}
    (hδnonneg : 0 ≤ δ) (hδ : δ < 1) (hB : 0 ≤ B)
    (hnet : UnitSphereNet tests δ) (htests : ∀ y ∈ tests, ‖T y‖ ≤ B) (x : E) :
    ‖T x‖ ≤ (B / (1 - δ)) * ‖x‖ :=
  (T.le_opNorm x).trans (mul_le_mul_of_nonneg_right
    (opNorm_le_of_unitSphereNet T hδnonneg hδ hB hnet htests) (norm_nonneg x))

/-- The paper's choice of net radius gives exactly the prescribed loss κ. -/
theorem kappa_net_certificate (T : E →L[ℝ] F) {tests : Finset E} {κ c : ℝ}
    (hκ : 1 < κ) (hc : 0 ≤ c)
    (hnet : UnitSphereNet tests ((κ - 1) / (κ + 1)))
    (htests : ∀ y ∈ tests, ‖T y‖ ≤ (1 + (κ - 1) / (κ + 1)) * c) (x : E) :
    ‖T x‖ ≤ κ * c * ‖x‖ := by
  have hden : 0 < κ + 1 := by linarith
  have hδ0 : 0 ≤ (κ - 1) / (κ + 1) := div_nonneg (by linarith) (le_of_lt hden)
  have hδ1 : (κ - 1) / (κ + 1) < 1 := by
    apply (div_lt_one hden).mpr
    linarith
  have hidentity :
      ((1 + (κ - 1) / (κ + 1)) * c) / (1 - (κ - 1) / (κ + 1)) = κ * c := by
    field_simp
    ring
  simpa [hidentity] using norm_apply_le_of_unitSphereNet T hδ0 hδ1
    (mul_nonneg (by linarith) hc) hnet htests x

















end FiniteNet

section Constants

/-- The Collins--Youn coefficient, with `q = (1+9/K)^n` and `L = K^n`. -/
noncomputable def freeNormConstant (L q : ℝ) : ℝ := Real.sqrt ((q - 1) / L)



theorem freeNormConstant_pos {L q : ℝ} (hL : 0 < L) (hq : 1 < q) :
    0 < freeNormConstant L q :=
  Real.sqrt_pos.mpr (div_pos (sub_pos.mpr hq) hL)

theorem freeNormConstant_sq {L q : ℝ} (hL : 0 < L) (hq : 1 ≤ q) :
    freeNormConstant L q ^ 2 = (q - 1) / L := by
  exact Real.sq_sqrt (div_nonneg (sub_nonneg.mpr hq) (le_of_lt hL))

/-- Scalar identity used when substituting the norm certificate into purity. -/
theorem purity_factor_identity {L q κ : ℝ} (hL : 0 < L) (hq : 1 ≤ q) :
    1 + L * (κ * freeNormConstant L q) ^ 2 = κ ^ 2 * q + 1 - κ ^ 2 := by
  rw [mul_pow, freeNormConstant_sq hL hq]
  field_simp
  ring

/-- For `κ ≥ 1` the negative correction may be dropped. -/
theorem purity_factor_le {L q κ : ℝ} (hL : 0 < L) (hq : 1 ≤ q) (hκ : 1 ≤ κ) :
    1 + L * (κ * freeNormConstant L q) ^ 2 ≤ κ ^ 2 * q := by
  rw [purity_factor_identity hL hq]
  nlinarith

/-- The exact constant `c_n` used throughout the manuscript. -/
noncomputable def collinsYounConstant (K n : ℕ) : ℝ :=
  freeNormConstant ((K : ℝ) ^ n) ((1 + 9 / (K : ℝ)) ^ n)

theorem collinsYounConstant_pos {K n : ℕ} (hK : 2 ≤ K) (hn : 1 ≤ n) :
    0 < collinsYounConstant K n := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  apply freeNormConstant_pos (pow_pos hKpos n)
  apply one_lt_pow₀
  · have := div_pos (by norm_num : (0 : ℝ) < 9) hKpos
    linarith
  · exact Nat.ne_of_gt (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)



/-- Specialized scalar purity estimate for the exact channel-output dimension. -/
theorem collinsYoun_purity_factor_le {K n : ℕ} {κ : ℝ} (hK : 2 ≤ K) (hκ : 1 ≤ κ) :
    1 + (K : ℝ) ^ n * (κ * collinsYounConstant K n) ^ 2 ≤
      κ ^ 2 * (1 + 9 / (K : ℝ)) ^ n := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  apply purity_factor_le (pow_pos hKpos n) _ hκ
  apply one_le_pow₀
  have := div_nonneg (by norm_num : (0 : ℝ) ≤ 9) (le_of_lt hKpos)
  linarith

end Constants

end Nonadditivity


