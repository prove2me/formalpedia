-- Prove2me | Definitions.Def_Probability_NormalityConnector
-- name    : Probability_NormalityConnector
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:25:27.362617+00:00
-- url     : https://prove2.me/theorems/cee7167a-4905-4ebb-b44e-f8dedb142fce
-- title:
--   Aether Catalog definitions — Probability_NormalityConnector
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.NormalityConnector`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/NormalityConnector.lean by skeleton subtraction
import Mathlib

/-!
# Normality and equidistribution

This file does **not** assert that any currently inaccessible constant (such as `π`, `e`,
or `√2`) is normal.  Instead it proves the structural bridge used by such a result:
equidistribution of the multiplicative orbit modulo one forces every finite base-`b`
digit block to have its expected frequency.
-/

namespace NormalityConnector

open Filter Set
open scoped Topology

/-- The empirical frequency of a predicate along the first `N` terms of a sequence. -/
noncomputable def empiricalFrequency (P : ℕ → Prop) [DecidablePred P] (N : ℕ) : ℝ :=
  ((Finset.filter P (Finset.range N)).card : ℝ) / N

/-- A sequence is interval-equidistributed in `[0,1)` when every half-open interval
has its length as asymptotic empirical frequency. -/
def IntervalEquidistributed (u : ℕ → ℝ) : Prop :=
  ∀ a c : ℝ, 0 ≤ a → a < c → c ≤ 1 →
    Tendsto (empiricalFrequency (fun n => u n ∈ Ico a c)) atTop (𝓝 (c - a))

/-- The length-`k` base-`b` block seen at position `n` in the expansion of `x`.
It is encoded as an integer from `0` through `b^k-1`. -/
noncomputable def digitBlock (b k : ℕ) (x : ℝ) (n : ℕ) : ℤ :=
  ⌊Int.fract ((b : ℝ) ^ n * x) * (b : ℝ) ^ k⌋

/-- Base-`b` normality, phrased as uniform limiting frequency of every finite digit
block in the fractional expansion. -/
def BaseNormal (b : ℕ) (x : ℝ) : Prop :=
  2 ≤ b ∧ ∀ k : ℕ, 0 < k → ∀ A : ℕ, A < b ^ k →
    Tendsto (empiricalFrequency (fun n => digitBlock b k x n = (A : ℤ)))
      atTop (𝓝 (1 / (b : ℝ) ^ k))



end NormalityConnector


