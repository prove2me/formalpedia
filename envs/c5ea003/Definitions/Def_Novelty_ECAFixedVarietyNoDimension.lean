-- Prove2me | Definitions.Def_Novelty_ECAFixedVarietyNoDimension
-- name    : Novelty_ECAFixedVarietyNoDimension
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:17:57.521333+00:00
-- url     : https://prove2.me/theorems/f297a08a-ac72-4a58-93c9-8848b8280671
-- title:
--   Aether Catalog definitions — Novelty_ECAFixedVarietyNoDimension
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ECAFixedVarietyNoDimension`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ECAFixedVarietyNoDimension.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Novelty_ECAFixedVarietyCore
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

namespace ECAFixedVariety

/-- Stationarity of a configuration is decidable on a finite ring. -/
instance decidableMemFixedSet (rule n : ℕ) [NeZero n] (s : Cfg n) :
    Decidable (s ∈ fixedSet rule n) :=
  inferInstanceAs (Decidable (step rule s = s))

/-! ### Obstruction 1: odd rules miss the origin -/





/-! ### Obstruction 2: a Lagrange bound on affine subvarieties -/

/-- `S` is an affine subvariety of `𝔸ⁿ_{𝔽₂}`: a translate of a linear subspace.
This is the weakest reading of "`S` has a dimension". -/
def IsAffineSubvariety {n : ℕ} (S : Set (Cfg n)) : Prop :=
  ∃ (v : Cfg n) (W : Submodule (ZMod 2) (Cfg n)), S = (fun w => v + w) '' (W : Set (Cfg n))




/-! ### The majority Rule 232 -/





/-! ### Rule 45 again: not even affine -/



/-! ### Synthesis -/


end ECAFixedVariety


