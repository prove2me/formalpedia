-- Prove2me | Definitions.Def_Nonadditivity_Asymptotics
-- name    : Nonadditivity_Asymptotics
-- status  : Definition
-- author  : @JWang226
-- created : 2026-10-07T20:20:52.60902+00:00
-- url     : https://prove2.me/theorems/807c729e-2c2a-44c0-b497-0c47577df447
-- title:
--   Rounded block length and separation bounds
-- statement:
--   For a natural number $K$, define the integer block length $n_K=\lceil K/\sqrt{\log K}\rceil$. The single-use upper comparison is $u_K=9n_K/(K\log2)+1/K$, and the half-two-use lower comparison is $\ell_K=n_K\log K/(2K\log2)$. The logarithm and the block length are positive for $K\ge2$. These explicit comparison functions supply the scalar quantities used in the channel separation limits.
-- source:
--   https://github.com/JWang226/Holevo-Additivity-Gap/blob/635aa93eb3a2310b79fd5371e2ce311914ec5887/Nonadditivity/Asymptotics.lean#L31-L53

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-
Copyright (c) 2026 the Nonadditivity project contributors.
All rights reserved. See COPYRIGHT.md for licensing and attribution.
-/










/-!
# Asymptotic consequences of the numerical channel bounds

The sequence `blockLength K = ⌈K / √(ln K)⌉₊` is the actual sequence in
Corollary 4 (vanishing Holevo information and diverging capacity).
The scalar limits below are unconditional theorems of real analysis.
The channel-specific conclusion takes the proved numerical bounds as explicit
hypotheses; it does not assert or axiomatize the random-channel construction.
-/

namespace Nonadditivity.Asymptotics

open Filter Topology

noncomputable section

/-- The exact integer block length in the separation corollary. -/
def blockLength (K : ℕ) : ℕ := ⌈(K : ℝ) / Real.sqrt (Real.log K)⌉₊

/-- Upper bound for the single-use Holevo information, in bits. -/
def separationUpper (K : ℕ) : ℝ :=
  9 * (blockLength K : ℝ) / ((K : ℝ) * Real.log 2) + 1 / (K : ℝ)

/-- Lower bound for half of the two-use Holevo information, in bits. -/
def separationLower (K : ℕ) : ℝ :=
  (blockLength K : ℝ) * Real.log K / (2 * (K : ℝ) * Real.log 2)



lemma log_nat_pos {K : ℕ} (hK : 2 ≤ K) : 0 < Real.log (K : ℝ) := by
  apply Real.log_pos
  exact_mod_cast (show 1 < K by omega)

lemma blockLength_pos {K : ℕ} (hK : 2 ≤ K) : 0 < blockLength K := by
  unfold blockLength
  apply Nat.ceil_pos.2
  apply div_pos
  · exact_mod_cast (show 0 < K by omega)
  · exact Real.sqrt_pos.2 (log_nat_pos hK)





















































end

end Nonadditivity.Asymptotics


