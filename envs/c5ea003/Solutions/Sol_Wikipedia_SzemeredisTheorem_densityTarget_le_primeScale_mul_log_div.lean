-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.densityTarget_le_primeScale_mul_log_div
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T09:59:35.027454+00:00
-- url     : https://prove2.me/submissions/6598e5c0-e13c-49e8-89ac-f3080dc8e11c

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section




/-!
# Quantitative parameters for the Green--Tao argument

This file fixes deliberately coarse constants for the sieve and
transference layers.  The important feature is their dependency order:
`maxAPForms`, `sieveExponent`, and `primeScale` depend only on the
progression length (and the fixed smooth-cutoff normalizer), while
`sieveLevel` is the first parameter that depends on the cyclic modulus.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Real













theorem maxAPForms_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < maxAPForms k := by
  exact Nat.mul_pos (by omega) (pow_pos (by norm_num) _)

theorem sieveExponent_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < sieveExponent k := by
  rw [sieveExponent]
  apply inv_pos.mpr
  exact_mod_cast
    Nat.mul_pos (by norm_num) (maxAPForms_pos hk)



theorem primeScale_pos {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    0 < primeScale k cutoffNormalizer := by
  rw [primeScale]
  exact lt_min (by norm_num)
    (div_pos (sieveExponent_pos hk)
      (mul_pos (by norm_num) hnorm))

theorem primeScale_nonneg {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    0 ≤ primeScale k cutoffNormalizer :=
  (primeScale_pos hk hnorm).le











theorem densityTarget_le_primeScale_mul_interval
    (k : ℕ) (cutoffNormalizer : ℝ) :
    densityTarget k cutoffNormalizer ≤
      primeScale k cutoffNormalizer *
        primeIntervalConstant / 100 := by
  exact min_le_right _ _











end Wikipedia.SzemeredisTheorem

end
/-!
# Quantitative parameters for the Green--Tao argument

This file fixes deliberately coarse constants for the sieve and
transference layers.  The important feature is their dependency order:
`maxAPForms`, `sieveExponent`, and `primeScale` depend only on the
progression length (and the fixed smooth-cutoff normalizer), while
`sieveLevel` is the first parameter that depends on the cyclic modulus.
-/
open Wikipedia.SzemeredisTheorem
open Filter Real

open Wikipedia.SzemeredisTheorem in
/-- The density obtained from Chebyshev is stronger than the deliberately
conservative target used by transference. -/
theorem solution
    {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    densityTarget k cutoffNormalizer ≤
      primeScale k cutoffNormalizer * log 2 / 128 := by
  calc
    densityTarget k cutoffNormalizer ≤
        primeScale k cutoffNormalizer *
          primeIntervalConstant / 100 :=
      densityTarget_le_primeScale_mul_interval k cutoffNormalizer
    _ ≤ primeScale k cutoffNormalizer * log 2 / 128 := by
      rw [primeIntervalConstant]
      have hproduct :
          0 ≤ primeScale k cutoffNormalizer * log 2 :=
        mul_nonneg (primeScale_nonneg hk hnorm)
          (log_pos (by norm_num)).le
      nlinarith
