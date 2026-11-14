-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Parameters
-- name    : GreenTaoPort_Wikipedia_GreenTao_Parameters
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:48:12.656258+00:00
-- url     : https://prove2.me/theorems/082dab5f-3d64-4fc9-be74-a708e3c6b29a
-- title:
--   Quantitative sieve and density parameters
-- statement:
--   The parameters depend on a progression length $k$, a cyclic modulus $N$, and a cutoff normalizer $c_\chi$. In the intended regime $k\ge3$, $N>0$, and $c_\chi>0$, set
--
--   $$
--   m_k=k2^{k-1},\qquad \theta_k=(100m_k)^{-1},\qquad R_k(N)=\lfloor N^{\theta_k}\rfloor,
--   $$
--
--   and define
--
--   $$
--   C=\frac{\log2}{4},\qquad
--   \alpha_k=\min\!\left\{\frac12,\frac{\theta_k}{8c_\chi}\right\},\qquad
--   \delta_k=\min\!\left\{\frac12,\frac{\alpha_k C}{100}\right\}.
--   $$
--
--   The quantity $m_k$ bounds the number of forms, $\theta_k$ controls the sieve exponent, $\alpha_k$ scales the prime weight, and $\delta_k$ is the target density for relative Szemerédi. The first quantities are chosen before the primorial cutoff and modulus; only the sieve level $R_k(N)$ depends on $N$. The formal functions also have their totalized values at degenerate inputs.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Parameters.lean#L19-L49

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic
import Lean

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3


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

/-- A coarse upper bound for the number of affine-linear forms occurring
in any Boolean expansion of a `k`-term progression system. -/
def maxAPForms (k : ℕ) : ℕ :=
  k * 2 ^ (k - 1)

/-- The small power of the cyclic modulus used as the sieve level. -/
noncomputable def sieveExponent (k : ℕ) : ℝ :=
  (100 * maxAPForms k : ℝ)⁻¹

/-- The truncated-divisor-sum level. -/
noncomputable def sieveLevel (k N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ sieveExponent k⌋₊

/-- The absolute constant supplied by the quarter-interval Chebyshev
lower bound. -/
noncomputable def primeIntervalConstant : ℝ :=
  log 2 / 4

/-- A fixed scaling of the W-tricked von Mangoldt weight.  The second
term in the minimum reserves ample exponent room for majorization. -/
noncomputable def primeScale (k : ℕ)
    (cutoffNormalizer : ℝ) : ℝ :=
  min (1 / 2)
    (sieveExponent k / (8 * cutoffNormalizer))

/-- The fixed density passed to relative Szemerédi.  It is chosen before
the W-trick cutoff and cyclic modulus. -/
noncomputable def densityTarget (k : ℕ)
    (cutoffNormalizer : ℝ) : ℝ :=
  min (1 / 2)
    (primeScale k cutoffNormalizer * primeIntervalConstant / 100)

































end Wikipedia.SzemeredisTheorem


/- Materialize compiler-generated declarations promised by this bundle. -/
run_meta do
  for requiredName in #[
    `Wikipedia.SzemeredisTheorem.densityTarget.eq_1,
    `Wikipedia.SzemeredisTheorem.primeIntervalConstant.eq_1,
    `Wikipedia.SzemeredisTheorem.primeScale.eq_1,
    `Wikipedia.SzemeredisTheorem.sieveExponent.eq_1,
    `Wikipedia.SzemeredisTheorem.sieveLevel.eq_1
  ] do
    let actualName ← Lean.realizeGlobalConstNoOverloadCore requiredName
    unless actualName == requiredName do
      throwError "Generated companion resolved to an unexpected name"


