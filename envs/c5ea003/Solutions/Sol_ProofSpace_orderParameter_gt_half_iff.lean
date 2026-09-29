-- Prove2me | solution 1 for ProofSpace.orderParameter_gt_half_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T17:52:13.739369+00:00
-- url     : https://prove2.me/submissions/bbb749c6-7c7f-468e-af3b-f94ebe736ab7

-- Sol generated from Logic/ProofSpaceTransition.lean
import Mathlib
import Definitions.Def_Logic_ProofSpaceTransition

/-!
# A discrete Gödel threshold in finite proof space

This file gives a precise finite model of the proposed phase-transition picture.
At cutoff `n`, `provable n` and `unprovable n` count the two classes of statements
seen so far.  Their difference is the signed order parameter.  The main theorem
shows that, whenever this difference starts positive and ends nonpositive, there
is a unique first cutoff at which the provable majority disappears.  Under a
strict-decrease hypothesis, the sign change is permanent and its location is
unique.

This is deliberately a theorem about an abstract enumeration: incompleteness
alone does not imply any particular asymptotic density or power law without a
choice of syntax, length function, and probability measure.
-/

open ProofSpace













open ProofSpace in
theorem solution{p u : ℕ} (htotal : 0 < p + u) :
    (1 / 2 : ℚ) < orderParameter p u ↔ u < p := by
  unfold orderParameter
  have hpos : (0 : ℚ) < ↑p + ↑u := by
    norm_cast
  rw [div_lt_div_iff₀ (by norm_num : (0 : ℚ) < 2) hpos]
  constructor
  · intro h
    norm_cast at h
    linarith
  · intro h
    norm_cast
    linarith
