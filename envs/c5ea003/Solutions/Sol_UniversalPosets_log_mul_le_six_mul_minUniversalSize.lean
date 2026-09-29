-- Prove2me | solution 1 for UniversalPosets.log_mul_le_six_mul_minUniversalSize
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T07:35:16.547389+00:00
-- url     : https://prove2.me/submissions/143d9735-230b-46ac-8224-b955c66ef1b2

-- Sol generated from Cryptography/UniversalPosets/ChainFamily.lean
import Mathlib
import Definitions.Def_Cryptography_UniversalPosets_ChainFamily
import Definitions.Def_Cryptography_UniversalPosets_MinSize
import Definitions.Def_Cryptography_UniversalPosets_ThreePosetBound
import Theorems.Thm_UniversalPosets_minUniversalSize_mono
import Theorems.Thm_UniversalPosets_two_mul_mul_pow_le_three_mul_minUniversalSize

/-!
# A superlinear lower bound: `U(n) ≥ n·log₄ n / 6`

`ExactSmall.lean` and `ThreePosetBound.lean` extract lower bounds for
`U(n) = minUniversalSize n` from the *overlap* method: two `n`-element posets
whose largest common induced subposet has `s` points force `2n - s` host points,
and a Bonferroni argument extends this to three posets, giving the linear bound
`3n - ⌈n/2⌉ - 3`.

This file pushes the overlap method to a family of `k` posets and shows that it
is genuinely **superlinear**: it yields

`2·k·4^k ≤ 3·U(4^k)`,  hence  `n · log₄ n ≤ 6 · U(n)`  for all `n`,

so `U(n)/n → ∞`.  This is the lower half of conjecture C2(b) of
`FUTURE_DIRECTIONS.md` (the overlap method reaches order `n log n`).

The family is geometric: for `n = 4^k` and `0 ≤ i < k`, let

`blockChains n (4^i)` = the disjoint union of `4^{k-i}` chains, each of length
`4^i` (blocks of consecutive indices).

Two members of the family are structurally incompatible in a quantitative way:
an induced subposet common to `blockChains n (4^i)` and `blockChains n (4^j)`
with `j < i` has at most `4^{k-i}·4^j` points, because it splits into at most
`4^{k-i}` chains (one per block of the coarse poset) and every chain of it lives
inside a single block of the fine poset, hence has at most `4^j` points.  The
resulting pairwise overlaps sum to at most `k·4^k/3`, so the `k` copies of an
`n`-element poset fill at least `k·4^k − k·4^k/3 = 2k·4^k/3` host points.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer).  Ranked conjectures for this cycle: (1) the overlap
method is not limited to a bounded number of posets, but the gain per extra
poset decays; (2) with a *geometric* family of chain-unions the pairwise
overlaps form a geometric series and hence cost only a constant fraction of the
gain, giving `Ω(n log n)`; (3) with a *linear* family (`d = 1, 2, 3, …`) the
overlaps dominate and nothing is gained; (4) no family can beat `O(n log n)`,
since by Dilworth any two `n`-element posets share a chain or an antichain on
`Ω(log n)` points.

Experiment (Experimenter).  (1) and (2) are formalised below
(`family_lower_bound`, `two_mul_mul_pow_le_three_mul_minUniversalSize`).  For
(3) the same computation with ratio `2` instead of `4` gives
`k·n − k·n = 0`: the geometric series `Σ 2^{i-j}` is exactly `1` per index, so
ratio `2` is the exact threshold of the method — this is why the base `4`
appears.  (4) is left open and restated in `FUTURE_DIRECTIONS.md`.

Analysis (Analyst).  The bound proved here is superlinear but still far below
the counting bound `2^{(n-1)/4} ≤ U(n)` of `LogBounds.lean`; its interest is
methodological: it measures exactly how much *structure* (as opposed to
counting) can force.  The threshold phenomenon at ratio `2` explains why the
three-poset bound of the previous cycle stalled at `5n/2`.

Critique (Critic).  All hypotheses of the Bonferroni step are discharged for the
explicit family; the pairwise bound is proved for arbitrary block sizes (not
just powers of `4`), and the arithmetic is carried out in `ℕ` with the exact
geometric identity `3·Σ_{j<i} 4^j + 1 = 4^i`, so no rounding is hidden.
-/

open UniversalPosets

open Function

/-! ## Monotonicity of the overlap bound -/


/-! ## Disjoint unions of chains of a fixed block size -/






/-! ## A Bonferroni bound for a family of sets -/


/-! ## The family lower bound -/


/-! ## The geometric family -/





/-! ## The general form -/




open UniversalPosets in
theorem solution(n : ℕ) :
    Nat.log 4 n * n ≤ 6 * minUniversalSize n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  set k := Nat.log 4 n with hk
  have hle : 4 ^ k ≤ n := Nat.pow_log_le_self 4 (by omega)
  have hlt : n < 4 ^ (k + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
  have hmono : minUniversalSize (4 ^ k) ≤ minUniversalSize n := minUniversalSize_mono hle
  have hbase := two_mul_mul_pow_le_three_mul_minUniversalSize k
  -- `n < 4·4^k`, so `k·n ≤ 4·k·4^k ≤ 6·U(n)`
  have hn4 : n ≤ 4 * 4 ^ k := by
    have : (4 : ℕ) ^ (k + 1) = 4 * 4 ^ k := by ring
    omega
  have hstep : k * n ≤ k * (4 * 4 ^ k) := Nat.mul_le_mul_left _ hn4
  have hstep2 : 2 * (k * 4 ^ k) ≤ 3 * minUniversalSize n := by
    have := Nat.mul_le_mul_left 3 hmono
    omega
  have : k * (4 * 4 ^ k) = 2 * (2 * (k * 4 ^ k)) := by ring
  calc k * n ≤ k * (4 * 4 ^ k) := hstep
    _ = 2 * (2 * (k * 4 ^ k)) := this
    _ ≤ 2 * (3 * minUniversalSize n) := Nat.mul_le_mul_left _ hstep2
    _ = 6 * minUniversalSize n := by ring
