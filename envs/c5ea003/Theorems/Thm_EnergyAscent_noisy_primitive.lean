-- Prove2me | Theorems.Thm_EnergyAscent_noisy_primitive
-- name    : EnergyAscent.noisy_primitive
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:16:06.251105+00:00
-- url     : https://prove2.me/theorems/a7caaa75-da4e-40a6-876c-3bf14275731a
-- title:
--   Primitivity of the family for even `k`, from explicit Bézout certificates
-- statement:
--   Primitivity of the family for even `k`, from explicit Bézout certificates
--   for each pair of factors of `a = (3k+1)(7k+1)` and `b = 2·2·k·(5k+1)`.
--
--   ```lean
--   theorem EnergyAscent.noisy_primitive(j : ℤ) :
--       Int.gcd (noisy (2 * j)).1 (noisy (2 * j)).2.1 = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EnergyAscentChannel.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EnergyAscentChannel.lean#L109

-- Thm stub generated from Combinatorics/EnergyAscentChannel.lean
import Mathlib
import Definitions.Def_Combinatorics_EnergyAscentChannel
import Definitions.Def_Combinatorics_EnergyAscentPellSpine

/-!
# Energy-Ascent V: the magnitude channel, its positive dependence and its ceiling

Energy-Ascent III showed that above scale `112·W` a Fermat-window hit forces the
middle ratio band, and Energy-Ascent IV showed that hits occur at every scale.
Here we draw the two information-theoretic consequences that the experimental
round reported, in exact combinatorial form.

* **Positive dependence** (the measured `MI = 0.1836 bits`, `z ≈ +110`):
  on *any* finite family of admissible triples that contains at least one hit
  and at least one triple outside the middle band, the empirical conditional
  frequency of letter `1` given a hit *strictly exceeds* its marginal
  frequency — `EnergyAscent.empirical_positive_dependence`.  Equivalently the
  empirical mutual information of the pair (hit bit, letter) is strictly
  positive.

* **A ceiling on the value** (the reported "value bounded, ~19%"): the channel
  is strictly noisy in the other direction.  We construct an explicit primitive
  family `noisy k` sitting in the middle band at every scale which the window
  never sees — `EnergyAscent.noisy_not_hit`.  So the letter does not determine
  the hit bit, and the window bit cannot be upgraded to an equivalence.

Both statements are unconditional theorems, not sample statistics.
-/

open EnergyAscent

open scoped Classical






/-! ## The ceiling: an unseeable middle-band family -/

theorem EnergyAscent.noisy_primitive(j : ℤ) :
    Int.gcd (noisy (2 * j)).1 (noisy (2 * j)).2.1 = 1 := by sorry
