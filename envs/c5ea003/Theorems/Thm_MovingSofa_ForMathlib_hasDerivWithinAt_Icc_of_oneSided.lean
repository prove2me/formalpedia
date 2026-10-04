-- Prove2me | Theorems.Thm_MovingSofa_ForMathlib_hasDerivWithinAt_Icc_of_oneSided
-- name    : MovingSofa.ForMathlib.hasDerivWithinAt_Icc_of_oneSided
-- status  : Proved
-- author  : @Tamas Fulop
-- created : 2026-10-03T20:52:11.844982+00:00
-- url     : https://prove2.me/theorems/138d196f-afb8-4d9e-a6bb-945ff6f350ea
-- title:
--   Glue one-sided derivatives on a closed interval
-- statement:
--   One-sided derivatives agreeing from both sides glue to a two-sided derivative on a closed interval, including endpoints.
-- source:
--   ForMathlib/Analysis/Calculus/Interval.lean

import Mathlib.Analysis.Calculus.ContDiff.Deriv
open Set

namespace MovingSofa.ForMathlib

theorem hasDerivWithinAt_Icc_of_oneSided {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b t : ℝ} (hab : a < b)
    (ht : t ∈ Icc a b) {f : ℝ → E} {d : E}
    (hr : t < b → HasDerivWithinAt f d (Ici t) t)
    (hl : a < t → HasDerivWithinAt f d (Iic t) t) :
    HasDerivWithinAt f d (Icc a b) t := by sorry

end MovingSofa.ForMathlib
