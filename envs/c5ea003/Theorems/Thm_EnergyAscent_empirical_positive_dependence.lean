-- Prove2me | Theorems.Thm_EnergyAscent_empirical_positive_dependence
-- name    : EnergyAscent.empirical_positive_dependence
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:16:40.378035+00:00
-- url     : https://prove2.me/theorems/2abf75a7-75c9-4453-aa6e-006c5c5964be
-- title:
--   Positive empirical dependence.
-- statement:
--   **Positive empirical dependence.**  On any finite family of admissible
--   triples containing a hit and a triple outside the middle band,
--   `P(letter = 1 | hit) > P(letter = 1)`, written multiplicatively so that no
--   division is needed.  This is the exact combinatorial form of a strictly
--   positive mutual information between the magnitude channel and the tree letter.
--
--   ```lean
--   theorem EnergyAscent.empirical_positive_dependence{W : ℤ} (hW : 0 < W)
--       (F : Finset (ℤ × ℤ × ℤ)) (hF : ∀ T ∈ F, Admissible W T)
--       (hhit : ∃ T ∈ F, InWindow W T) (hbad : ∃ T ∈ F, ¬ LetterOne T) :
--       (F.filter (fun T => LetterOne T)).card * (F.filter (fun T => InWindow W T)).card <
--         (F.filter (fun T => InWindow W T ∧ LetterOne T)).card * F.card := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/EnergyAscentChannel.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/EnergyAscentChannel.lean#L55

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

theorem EnergyAscent.empirical_positive_dependence{W : ℤ} (hW : 0 < W)
    (F : Finset (ℤ × ℤ × ℤ)) (hF : ∀ T ∈ F, Admissible W T)
    (hhit : ∃ T ∈ F, InWindow W T) (hbad : ∃ T ∈ F, ¬ LetterOne T) :
    (F.filter (fun T => LetterOne T)).card * (F.filter (fun T => InWindow W T)).card <
      (F.filter (fun T => InWindow W T ∧ LetterOne T)).card * F.card := by sorry
