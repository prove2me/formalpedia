-- Prove2me | Definitions.Def_ErdosProblems_Erdos269_ResidueEscape
-- name    : ErdosProblems_Erdos269_ResidueEscape
-- status  : Definition
-- author  : @willcook
-- created : 2026-09-27T18:11:42.213888+00:00
-- url     : https://prove2.me/theorems/c6789cf1-9d22-43a8-ba1e-22ceacbeae68
-- title:
--   ResidueEscape
-- statement:
--   Defines the least positive representative modulo C, using C for the zero class, and a window-escape predicate comparing that representative with a proposed bound.
-- source:
--   Lean source (Apache-2.0): https://github.com/wcook04/plectis-erdos-lean/blob/cc7e541cf2081c6fef5a5e377d52e365e33b01eb/ErdosProblems/Erdos269/ResidueEscape.lean#L1-L187
--   Related paper by Will Cook (CC-BY-4.0): https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L1-L260
--   Paper prior-art bibliography: https://github.com/wcook04/plectis-erdos/blob/551bae6dc6e732cf85172d66323c8d2bc77ba962/paper/269/erdos-269-three-prime-running-lcm.tex#L681-L689

import Mathlib.Data.Int.ModEq
import Mathlib.Tactic

/-!
# Erdős #269: the finite least-positive-residue obstruction

For a positive modulus `C`, the least positive representative of a congruence
class is `C` for the zero class and lies in `1, ..., C - 1` otherwise.  Hence a
positive integer state bounded by `K` cannot be congruent to an integer whose
least positive representative is larger than `K`.

This module proves only that final finite obstruction.  An application to the
series in Erdős problem #269 still needs two upstream inputs: rationality must
produce a positive bounded integral state with the required smooth-divisibility
congruence, and one must construct arbitrarily late finite windows whose least
positive residues escape the corresponding bound.  Neither input, and hence no
irrationality theorem for the series, is proved here.
-/

namespace ErdosProblems.Erdos269

/-- Canonical positive representative of an integer modulo `C`: a zero
residue is represented by `C`, and every nonzero residue by its nonnegative
Euclidean remainder.  The definition is total at `C = 0`, but all theorems
using its positive-representative meaning assume `0 < C`. -/
def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))





/-- The numerical predicate `bound < residue ≤ C`. -/
def ResidueEscapesWindow (C bound residue : ℕ) : Prop :=
  bound < residue ∧ residue ≤ C









/-! ## Affine-cylinder endpoint nesting -/



end ErdosProblems.Erdos269


