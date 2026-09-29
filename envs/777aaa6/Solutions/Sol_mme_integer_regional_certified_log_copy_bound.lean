-- Prove2me | solution 1 for mme_integer_regional_certified_log_copy_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-21T20:05:06.442366+00:00
-- url     : https://prove2.me/submissions/78b940c0-fbb1-42b0-95ac-f861cc67fd4c

import Definitions.Def_mme_regional_certified_log_copy_bound
import Mathlib
open BigOperators MME MME.RegionRate MME.RegionRealization
set_option autoImplicit false
set_option maxHeartbeats 1000000

private theorem rounded_copies (x a : ℝ) (b : ℕ) (hb : 0 < b)
    (ha : 0 ≤ a) (hx : 2 * (b : ℝ) * Real.exp a ≤ x) :
    Real.exp a ≤ ((⌊x⌋₊ / b : ℕ) : ℝ) := by
  have he : 1 ≤ Real.exp a := Real.one_le_exp_iff.mpr ha
  have hc : (⌈Real.exp a⌉₊ : ℝ) ≤ 2 * Real.exp a := by
    have hh := Nat.ceil_le_floor_add_one (Real.exp a)
    have hf := Nat.floor_le (Real.exp_pos a).le
    have hh' : (⌈Real.exp a⌉₊ : ℝ) ≤ (⌊Real.exp a⌋₊ : ℝ) + 1 := by
      exact_mod_cast hh
    linarith
  have hprod : (⌈Real.exp a⌉₊ * b : ℕ) ≤ ⌊x⌋₊ := by
    apply Nat.le_floor
    push_cast
    calc
      (⌈Real.exp a⌉₊ : ℝ) * b ≤ (2 * Real.exp a) * b :=
        mul_le_mul_of_nonneg_right hc (Nat.cast_nonneg b)
      _ = 2 * b * Real.exp a := by ring
      _ ≤ x := hx
  have hq : ⌈Real.exp a⌉₊ ≤ ⌊x⌋₊ / b := (Nat.le_div_iff_mul_le hb).mpr hprod
  exact (Nat.le_ceil (Real.exp a)).trans (by exact_mod_cast hq)

theorem solution {ell M : ℕ} {P : ProfiledCW.Predicate M}
    (D : IntegerStep ell M P) (a : ℝ) (ha : 0 ≤ a)
    (hbudget : a ≤ D.certifiedLogCopies) :
    Real.exp a ≤ (D.entropyCopies : ℝ) := by
  let F := scaleFactor (half := D.half) (parent := D.parent) D.n D.repairScale ell
  let T := polynomialFactor D.n (Fintype.card (RecursiveYZ.Cell D.half D.R D.parent))
  let X := regionalRate D.total D.n D.m D.mu - ((∑ r, D.n r : ℕ) : ℝ) *
      entropyModulus (Fin 2 → CompleteSplit.CompleteWord ell) D.epsilon -
      4 * Real.sqrt (Real.log F + scaleExponent D.total D.n D.m D.mu D.epsilon)
  have hF : 0 < F := by
    dsimp [F,scaleFactor,loadFactor,polynomialFactor,ambientFactor]
    positivity
  have hT : 0 < T := by dsimp [T,polynomialFactor]; positivity
  have hden : 0 < 64 * T * F := by positivity
  have hb : 0 < 8 ^ D.repairExponent := by positivity
  have hbR : 0 < ((8 ^ D.repairExponent : ℕ) : ℝ) := by exact_mod_cast hb
  have hblog : Real.log ((8 ^ D.repairExponent : ℕ) : ℝ) =
      D.repairExponent * Real.log 8 := by rw [Nat.cast_pow]; exact Real.log_pow 8 _
  have hbudget' : a + Real.log (64 * T * F) +
      Real.log ((8 ^ D.repairExponent : ℕ) : ℝ) ≤ X := by
    change a ≤ X - Real.log (64 * T * F) - D.repairExponent * Real.log 8 at hbudget
    rw [hblog]
    linarith
  have he := Real.exp_le_exp.mpr hbudget'
  rw [Real.exp_add, Real.exp_add, Real.exp_log hden, Real.exp_log hbR] at he
  have hbound : 2 * ((8 ^ D.repairExponent : ℕ) : ℝ) * Real.exp a ≤ D.entropyLower := by
    change 2 * ((8 ^ D.repairExponent : ℕ) : ℝ) * Real.exp a ≤
      Real.exp X / (32 * T * F)
    apply (le_div_iff₀ (by positivity : 0 < 32 * T * F)).mpr
    convert he using 1 <;> ring
  exact rounded_copies D.entropyLower a (8 ^ D.repairExponent) hb ha hbound
