-- Prove2me | Theorems.Thm_AdjSum_blockMat_coreStates_le
-- name    : AdjSum.blockMat_coreStates_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:11:44.930577+00:00
-- url     : https://prove2.me/theorems/3a070439-7896-423b-91f6-b1b9645dddfd
-- title:
--   BlockMat coreStates le
-- statement:
--   Formal statement of `AdjSum.blockMat_coreStates_le` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem AdjSum.blockMat_coreStates_le(s : ℕ) (a b : Fin (s + 1)) :
--       blockMat (coreStates s) a b ≤ adjMat s a b := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/AdjacentSumPolytopes/Growth.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/AdjacentSumPolytopes/Growth.lean#L143

-- Thm stub generated from Applications/AdjacentSumPolytopes/Growth.lean
import Mathlib
import Definitions.Def_Applications_AdjacentSumPolytopes_Basic
import Definitions.Def_Applications_AdjacentSumPolytopes_Growth
import Definitions.Def_Applications_AdjacentSumPolytopes_Recurrence

/-!
# Exponential growth of the adjacent-sum counts, and the two-state Fibonacci model

The recurrences of `Applications.AdjacentSumPolytopes.Recurrence` say *nothing* about
the size of the counts.  Here we bracket the growth of both parity classes by explicit
exponentials, using only entrywise nonnegativity of the transfer matrix — no
Perron–Frobenius theory is required:

`(⌊s/2⌋+1)^(d+1) ≤ #(cyclic points of length d+1) ≤ (s+1)^(d+1)`,
`(⌊s/2⌋+1)^(d+2) ≤ #(open points of length d+2)  ≤ (s+1)^(d+2)`.

The lower bound comes from the *core block* of states `a` with `2a ≤ s`: any two such
states are compatible, so the all-ones matrix on that block is entrywise below the
transfer matrix.  The upper bound compares with the all-ones matrix on all states.

Consequently the dominant real pole `1/λ_s` of the shared denominator satisfies
`1/(s+1) ≤ 1/λ_s ≤ 1/(⌊s/2⌋+1)`; in particular the counts grow strictly exponentially
as soon as `s ≥ 2` (`cycCount_two_pow_le`).

We also identify the two-state (`s = 1`) case completely: the open counts are Fibonacci
numbers and the cyclic counts are Lucas numbers.

-- !-- Lab Notes -- !--
* **Hypothesis.** The all-ones block on `{a : 2a ≤ s}` should already give the right
  order of growth; the true growth constant `λ_s` should sit strictly between
  `⌊s/2⌋+1` and `s+1` for `s ≥ 2`.
* **Experiment.** Cyclic counts for `s = 2` are `2, 6, 11, 26, 57, 129, 289, 650`;
  successive ratios `2.36, 2.26, 2.25, ...` approach the dominant root of
  `x³ − 2x² − x + 1`, which lies strictly between `⌊2/2⌋+1 = 2` and `3`.  For `s = 3`:
  `2, 10, 23, 70, 197, 571, 1640` with ratios approaching `≈ 2.87 ∈ (2, 4)`.
* **Analysis.** The block bound is tight in order of magnitude but not in constant;
  the ratio `λ_s/(⌊s/2⌋+1)` appears to converge, which we record as a conjecture.
* **Critique.** The bounds hold for every `s` and every `d` with no hypotheses, and are
  *strict* exponentials (base `≥ 2`) exactly when `s ≥ 2`; for `s = 0` both bounds
  collapse to `1`, correctly, since the only lattice point is the origin.
-/

open AdjSum

open Finset Matrix

/-! ## Monotonicity of powers of nonnegative matrices -/



/-! ## All-ones blocks -/






/-! ## The core block of mutually compatible states -/

theorem AdjSum.blockMat_coreStates_le(s : ℕ) (a b : Fin (s + 1)) :
    blockMat (coreStates s) a b ≤ adjMat s a b := by sorry
