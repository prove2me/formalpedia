-- Prove2me | Theorems.Thm_ECAFixedVariety_ncard_dvd_of_isAffineSubvariety
-- name    : ECAFixedVariety.ncard_dvd_of_isAffineSubvariety
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T15:32:27.300723+00:00
-- url     : https://prove2.me/theorems/10437729-60aa-4b29-8cfb-dbfde11bc810
-- title:
--   Lagrange obstruction.
-- statement:
--   **Lagrange obstruction.**  The cardinality of an affine subvariety of
--   `𝔸ⁿ_{𝔽₂}` divides `2ⁿ`.
--
--   ```lean
--   theorem ECAFixedVariety.ncard_dvd_of_isAffineSubvariety{n : ℕ} [NeZero n] {S : Set (Cfg n)}
--       (h : IsAffineSubvariety S) : S.ncard ∣ 2 ^ n := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/ECAFixedVarietyNoDimension.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/ECAFixedVarietyNoDimension.lean#L83

-- Thm stub generated from Novelty/ECAFixedVarietyNoDimension.lean
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
import Definitions.Def_Novelty_ECAFixedVarietyNoDimension
import Definitions.Def_Novelty_ECAFixedVarietyPeriodThree

/-!
# When the fixed-point "variety" has no dimension at all

The conjecture under test presupposes that `V(f) = {s : f(s) = s}` is a linear
(or at least affine) subvariety of `𝔸ⁿ_{𝔽₂}`, so that `dim V(f)` makes sense.
This file shows that the presupposition fails for *most* elementary cellular
automata, by two independent obstructions.

**Obstruction 1 (parity / origin).**  `V(f)` contains the origin iff the local
rule sends the zero neighbourhood to `0`, i.e. iff the Wolfram number is even.
Hence for all `128` odd rules the fixed locus is not a linear subspace, whatever
`n` is (`odd_rule_no_fixed_dim`).

**Obstruction 2 (Lagrange).**  An affine subvariety of `𝔸ⁿ_{𝔽₂}` has cardinality
dividing `2ⁿ` (`ncard_dvd_of_isAffineSubvariety`).  The majority Rule 232 has
exactly `6` stationary configurations on the ring of size `4`, and `6 ∤ 16`;
Rule 45 has exactly `3` on the ring of size `3`, and `3 ∤ 8`.  So these loci are
not even affine subvarieties (`rule232_not_affine`, `rule45_not_affine`).

Finally `wolfram_fixedpoint_dimension_conjecture_false` collects the falsifying
evidence: the class-4 Rule 110 has the *minimal* variety, the class-3 Rule 90
has dimension `≤ 2` no matter how large `n` is, the class-3 Rule 45 has an empty
variety for `3 ∤ n`, and the class-2 Rule 232 has no dimension at all.
-/

open ECAFixedVariety


/-! ### Obstruction 1: odd rules miss the origin -/





/-! ### Obstruction 2: a Lagrange bound on affine subvarieties -/

theorem ECAFixedVariety.ncard_dvd_of_isAffineSubvariety{n : ℕ} [NeZero n] {S : Set (Cfg n)}
    (h : IsAffineSubvariety S) : S.ncard ∣ 2 ^ n := by sorry
