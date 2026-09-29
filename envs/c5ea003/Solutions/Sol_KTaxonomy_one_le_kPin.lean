-- Prove2me | solution 1 for KTaxonomy.one_le_kPin
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T05:45:49.592689+00:00
-- url     : https://prove2.me/submissions/f634ce58-61c2-45cd-b593-a5e89b331e57

-- Sol generated from Cryptography/KTaxonomyGeneralWidth.lean
import Mathlib
import Definitions.Def_Cryptography_KTaxonomyCensusEcon

/-!
# The k-taxonomy at general (non-dyadic) support width

`Cryptography.KTaxonomyCensusEcon` settles the taxonomy for dyadic widths `W = 2 ^ m`,
where the census optimum is the exact two-element tie set `{m - 2, m - 1}`.  This file
removes the dyadic restriction: for an arbitrary width `W > 0` it characterises the census
argmin by a pair of *dyadic bracketing inequalities*, and derives from that characterisation
the two structural verdicts of the taxonomy at full generality:

* `census_argmin_iff` : `k` is a census optimum for width `W` iff `W ≤ 2 ^ (k + 2)` and
  (`k = 0` or `2 ^ (k + 1) ≤ W`).  For `W = 2 ^ m` this returns the tie set `{m-2, m-1}`,
  and in general it says the optimum sits at offset `-2` or `-1` relative to `log₂ W`.
* `census_pin_strictly_suboptimal` : for **every** integer width `W ≥ 2` the pin
  `⌈log₂ W⌉` is strictly beaten by `⌈log₂ W⌉ - 1`.  So the pin is never a census optimum —
  not merely for the dyadic widths checked numerically.
* `pin_gap_general` : for **every** integer width `W ≥ 2`, every census optimum `k`
  satisfies `kPin W - k ∈ {1, 2}`.
* `econ_argmin_iff` : the corresponding characterisation for the economics objective,
  obtained for free from the exact anchor identity `econ_eq_census_anchor`.

-- !-- Lab Notes -- !--
Hypothesizer (round 2, after the dyadic results):
 (H6) The `{-2, -1}` offset pattern is not a dyadic accident: it is the general shape of
      the census argmin, expressible as `2 ^ (k+1) ≤ W ≤ 2 ^ (k+2)`.              [BOLD]
 (H7) "Pin is never optimal" holds for every integer width, with a one-line reason:
      `W ≤ 2 ^ ⌈log₂ W⌉` forces the last query to cost more than the residual it saves.
 (H8) The gap `pin - argmin ∈ {1,2}` is a corollary of H6 plus the two clog bracketing
      inequalities `2 ^ (⌈log₂ W⌉ - 1) < W ≤ 2 ^ ⌈log₂ W⌉`, so it needs no case check.

Experimenter: H6–H8 proved below with zero sorries.  The only analytic ingredient is the
increment formula `census W (k+1) - census W k = 1 - W / 2 ^ (k+2)`; everything else is
the discrete-convexity principle `min_of_local_min` from the previous file plus `Nat.clog`
bracketing.

Analyst: the numerically observed statement "gap ∈ {1,2} for every W ≤ 4096" is therefore
not a finite check at all — it is a theorem for every `W`, and the two possible gap values
are exactly the two ends of the census tie bracket.  Nothing in the argument uses dyadicity,
which is the structural reason the tie set has exactly two elements when `W` is dyadic (both
bracketing inequalities become equalities) and one element otherwise.
-/

open KTaxonomy

/-! ## The increment of the census cost -/


/-! ## The census argmin at general width -/



/-! ## The pin is never optimal, at every integer width -/








open KTaxonomy in
theorem solution{W : ℕ} (hW : 2 ≤ W) : 1 ≤ kPin W :=
  Nat.clog_pos (by norm_num) (by omega)
