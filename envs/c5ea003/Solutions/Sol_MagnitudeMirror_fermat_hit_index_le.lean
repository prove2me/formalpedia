-- Prove2me | solution 1 for MagnitudeMirror.fermat_hit_index_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T23:56:27.638826+00:00
-- url     : https://prove2.me/submissions/d3c5ec46-c984-4bcf-b0b2-3d8f433e6ca2

-- Sol generated from Combinatorics/MagnitudeMirrorTransfer.lean
import Mathlib
import Definitions.Def_Combinatorics_MagnitudeMirrorSeal
import Theorems.Thm_MagnitudeMirror_fermat_hit_index_bound
/-
# Round-70 #6, cycle 2 — transfer beyond the magnitude: an exact characterisation
# of mirrors, the correct null, and the Fermat frontier cost law

Cycle 1 (`Combinatorics.MagnitudeMirrorSeal`) established that the realized
probes of papers 193/195 are structural constants or deterministic functions of
`N`'s magnitude, and that a magnitude mirror collapses to *exactly* zero
information inside every magnitude cell.  Cycle 2 asks the three questions the
critic raised against that synthesis.

1. **Is the collapse a characterisation, or only a consequence?**  It is a
   characterisation.  `zeroInfo_self_iff_const` shows that a statistic which is
   uninformative *about itself* is constant, and
   `mirror_iff_conditional_zeroInfo` upgrades this to: a feature collapses to
   exactly zero information inside every magnitude cell, against *every* secret,
   **iff** it is a deterministic function of the magnitude.  So "exact null given
   `|N|`" is not evidence-of-absence — it is *equivalent* to being a mirror.

2. **Why then did the row-shuffle null flag the mirror?**  Because a shuffle
   null tests the wrong hypothesis.  `zeroInfo_of_conditional_homogeneous` proves
   the exact converse direction: a mirror is *unconditionally* uninformative as
   soon as the secret's marginal is homogeneous across magnitude cells.  Hence
   `mirror_signal_forces_stratification`: if a mirror shows any unconditional
   signal at all, the secret's marginal provably varies across magnitude cells.
   Apparent signal from a deterministic function of `N` is scale stratification —
   a theorem, not a heuristic.

3. **What is the surviving geometry worth quantitatively?**  The Fermat frontier.
   `fermat_hit_index_bound` gives the exact ascent law
   `2·⌊√N⌋·j ≤ k² + 2·⌊√N⌋` for the offset `j` of the square-hit of
   `N = u(u+2k)` from the isqrt anchor, and `fermat_hit_index_le` turns it into
   the cost bound `j ≤ k²/(2⌊√N⌋) + 1`: the frontier distance is governed by the
   factor *imbalance* `k = (v−u)/2`, exactly the quantity the positional oracle
   `1{d ≤ B}` reads and no realized probe does.  Finally
   `oracle_capacity_superlevel_interval` shows the capacity profile of that
   oracle has interval superlevel sets, so the reported "`B*` for ≥90% of peak"
   is a well-defined threshold, not an artifact of the search grid.
-/

open MagnitudeMirror

open Finset Round11

variable {α : Type*} {β γ μ : Type*} [DecidableEq β] [DecidableEq γ] [DecidableEq μ]

/-! ## 1. Zero self-information means constant -/


/-! ## 2. Mirrors are exactly the features with an exact conditional null -/


/-! ## 3. The correct null: conditional collapse plus homogeneous marginals -/



/-! ## 4. The Fermat frontier: an exact ascent law for the square-hit offset -/




/-! ## 5. The oracle capacity profile has interval superlevel sets -/



/-! ## 6. Cycle 4: the frontier law is two-sided, and the capacity peak is exact
balance -/





open MagnitudeMirror in
theorem solution(u k : ℕ) (hm : 0 < Nat.sqrt (u * (u + 2 * k))) :
    (u + k) - Nat.sqrt (u * (u + 2 * k))
      ≤ k ^ 2 / (2 * Nat.sqrt (u * (u + 2 * k))) + 1 := by
  set m := Nat.sqrt (u * (u + 2 * k)) with hm'
  have hb := fermat_hit_index_bound u k
  rw [← hm'] at hb
  set j := (u + k) - m with hj
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · rw [h0]
    exact Nat.zero_le _
  have hstep : 2 * m * (j - 1) ≤ k ^ 2 := by
    have : 2 * m * j = 2 * m * (j - 1) + 2 * m := by
      have : j = (j - 1) + 1 := by omega
      nlinarith [this]
    omega
  set q := k ^ 2 / (2 * m) with hq
  have hqle : j - 1 ≤ q := (Nat.le_div_iff_mul_le (by omega)).2 (by linarith [hstep])
  omega
