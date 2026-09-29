-- Prove2me | Definitions.Def_Probability_Counting
-- name    : Probability_Counting
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:11:56.214705+00:00
-- url     : https://prove2.me/theorems/b1fbb9b1-6262-4454-8967-bba76b8eae44
-- title:
--   Aether Catalog definitions — Probability_Counting
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.Counting`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/Counting.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_Basic

/-!
# Counting representations: `1` and `2` are exceptional

Heath-Brown's conjecture predicts that for a *generic* admissible `n` the number of
representations `n = x³ + y³ + z³` with `max(|x|,|y|,|z|) ≤ B` grows like `c_n log B`.  The
integers `1` and `2` are famously exceptional: the classical one-parameter families give
`≫ B^{1/4}` and `≫ B^{1/3}` representations respectively, which is vastly more than
logarithmic.

This file makes those lower bounds explicit and formal:

* `ThreeCubes.card_repsBox_one` : at least `2T+1` representations of `1` inside the box of
  radius `12T⁴ + 9T³ + 3T + 1`, i.e. `≫ B^{1/4}` representations of height `≤ B`;
* `ThreeCubes.card_repsBox_two` : at least `2T+1` representations of `2` inside the box of
  radius `6T³ + 6T² + 1`, i.e. `≫ B^{1/3}` representations of height `≤ B`.
-/

namespace ThreeCubes

/-- The set of representations of `n` as an ordered sum of three cubes inside the box of
radius `B`. -/
noncomputable def repsBox (n : ℤ) (B : ℤ) : Finset (ℤ × ℤ × ℤ) :=
  ((Finset.Icc (-B) B) ×ˢ (Finset.Icc (-B) B) ×ˢ (Finset.Icc (-B) B)).filter
    (fun q => q.1 ^ 3 + q.2.1 ^ 3 + q.2.2 ^ 3 = n)






end ThreeCubes


