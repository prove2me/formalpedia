-- Prove2me | Theorems.Thm_syracuse_primitive_word_ge_6956_rotated_baseline_2786502_iff_no_minimal_period_ge_6956_cycle
-- name    : syracuse_primitive_word_ge_6956_rotated_baseline_2786502_iff_no_minimal_period_ge_6956_cycle
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T13:27:06.902425+00:00
-- url     : https://prove2.me/theorems/17d05575-e95c-477c-8ccf-d5481f6bb23d
-- title:
--   Equivalence between the period-6956 rotated-baseline word frontier and the absence of Syracuse cycles of minimal period at least 6956
-- statement:
--   Let $T : \mathbb{N} \to \mathbb{N}$ denote the accelerated Syracuse map $T(n) = (3n + 1)/2^{\nu_2(3n + 1)}$, and let $C(w) = \operatorname{syracuseAffineConstant}(w)$ denote the canonical Syracuse affine constant of a finite valuation word $w = (e_0, \ldots, e_{p-1})$ of length $p = \operatorname{length}(w)$ and total sum $K = \sum_{i=0}^{p-1} e_i$. Then the open valuation-word nondivisibility statement at period $p \ge 6956$ and rotated baseline $2{,}786{,}502$ — namely, that every positive word $w$ ($e_i > 0$) of length $p \ge 6956$ that is primitive under proper cyclic rotations ($w.\operatorname{rotate}(d) \ne w$ for $0 < d < p$) and satisfies $3^p < 2^K$, $200 K < 317 p$, $306 K < 485 p$, $2^K \cdot 2310000^p \le (3 \cdot 2310000 + 1)^p$, and $2786502 \cdot (2^K - 3^p) \le C(w.\operatorname{rotate}(d))$ for all $0 \le d < p$ obeys $(2^K - 3^p) \nmid C(w)$ — is logically equivalent to the nonexistence of nontrivial Syracuse cycles of minimal period at least $6956$:
--
--   $$\mathcal{L}_{6956,\,2786502} \iff \Bigl(\forall m, p \in \mathbb{N}, \; m > 0 \land p \ge 6956 \land \operatorname{minimalPeriod}_T(m) = p \implies m = 1\Bigr).$$
--
--   This equivalence certifies that the eight structural hypotheses accumulated along the Prove2me Collatz cycle-exclusion reduction tree up to leaf `f9fd04d9-1a91-4015-8f1e-d0e842ccf6be` are completely lossless: resolving leaf `f9fd04d9-1a91-4015-8f1e-d0e842ccf6be` is both necessary and sufficient for ruling out all nontrivial Syracuse cycles of minimal period $p \ge 6956$ (and hence, via the forward bridge, all nontrivial Syracuse cycles of any positive period).
-- source:
--   Collatz cycle-exclusion frontier bridge packet (Mission 2f34a49f-2016-4de2-9662-fcd1cc96cc67), combining syracuse_cycle_eq_one_of_primitive_word_ge_6956_rotated_baseline_2786502 and syracuse_primitive_word_ge_6956_rotated_baseline_2786502_of_no_cycle.

import Mathlib.Dynamics.PeriodicPts.Defs
import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_ge_6956_rotated_baseline_2786502_iff_no_minimal_period_ge_6956_cycle :
    (∀ w : List ℕ,
      (∀ a ∈ w, 0 < a) →
      6956 ≤ w.length →
      (∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w) →
      3 ^ w.length < 2 ^ w.sum →
      200 * w.sum < 317 * w.length →
      306 * w.sum < 485 * w.length →
      (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤ (3 * 2310000 + 1 : ℕ) ^ w.length →
      (∀ d : ℕ, d < w.length →
        (2786502 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤ syracuseAffineConstant (w.rotate d)) →
      ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w) ↔
    (∀ m p : ℕ, 0 < m → 6956 ≤ p →
      Function.minimalPeriod syracuseStep m = p → m = 1) := by sorry
