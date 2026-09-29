-- Prove2me | Definitions.Def_MachineLearning_WignerSemicircle_Moments
-- name    : MachineLearning_WignerSemicircle_Moments
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:20:17.293474+00:00
-- url     : https://prove2.me/theorems/af2e7ca2-17b6-4ec2-8521-cbb7501ae020
-- title:
--   Aether Catalog definitions — MachineLearning_WignerSemicircle_Moments
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.WignerSemicircle.Moments`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/WignerSemicircle/Moments.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license.

# Moments of the Wigner Semicircle Distribution

The Wigner semicircle law states that the empirical spectral distribution of a
Wigner random matrix converges weakly to the semicircle distribution.  The
combinatorial heart of the *moment method* proof is the following fact: the
moments of the (standard, radius-2) semicircle distribution are exactly the
**Catalan numbers**,

  m_{2k} = C_k,   m_{2k+1} = 0,

and these numbers satisfy the Catalan recurrence

  C_{n+1} = ∑_{i=0}^{n} C_i · C_{n-i}.

This recurrence is precisely the recurrence one obtains for the limiting expected
traces `(1/N) E tr(W^{2k})` of a Wigner ensemble via the non-crossing pair
partition (Dyck path) enumeration.  This file develops this moment sequence as a
real-valued function on `ℕ` and proves the chain of facts that make it the unique
candidate limit in the moment method.

## Main results

- `scMoment_zero`        — the 0-th moment is 1 (total mass).
- `scMoment_odd`         — all odd moments vanish (symmetry).
- `scMoment_two_mul`     — the `2k`-th moment equals `catalan k`.
- `scMoment_recurrence`  — the Wigner/Catalan moment recurrence.
- `scMoment_centralBinom`— closed form via the central binomial coefficient.
- `scMoment_le_four_pow` — the Carleman-type growth bound `m_{2k} ≤ 4^k`,
                           which guarantees the moment problem is determinate.
- concrete values `scMoment_two`, `scMoment_four`, `scMoment_six`.
-/

namespace MachineLearning.WignerSemicircle

open scoped BigOperators

/-- The moment sequence of the standard semicircle distribution: the `n`-th
moment is `catalan (n/2)` for even `n` and `0` for odd `n`. -/
noncomputable def scMoment (n : ℕ) : ℝ :=
  if Even n then (catalan (n / 2) : ℝ) else 0











end MachineLearning.WignerSemicircle


