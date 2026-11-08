-- Prove2me | Theorems.Thm_syracuse_cycle_eq_one_of_primitive_word_ge_6956_rotated_baseline_2786502
-- name    : syracuse_cycle_eq_one_of_primitive_word_ge_6956_rotated_baseline_2786502
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T13:27:06.440895+00:00
-- url     : https://prove2.me/theorems/a3ea9227-e3f3-47b2-b98d-8fdbe27dc9ef
-- title:
--   Conditional exclusion of all nontrivial Syracuse cycles from the period-6956 rotated-baseline word frontier
-- statement:
--   Let $T : \mathbb{N} \to \mathbb{N}$ denote the accelerated Syracuse map $T(n) = (3n + 1)/2^{\nu_2(3n + 1)}$, and let $C(w) = \operatorname{syracuseAffineConstant}(w)$ denote the canonical Syracuse affine constant of a valuation word $w = (e_0, \ldots, e_{q-1}) \in \mathbb{N}^q$ with length $q = \operatorname{length}(w)$ and sum $K = \sum_{i=0}^{q-1} e_i$. Suppose that for every word $w$ of positive integers ($e_i > 0$) with length $q \ge 6956$ that is primitive under proper cyclic rotations ($w.\operatorname{rotate}(d) \ne w$ for all $0 < d < q$) and satisfies
--
--   $$3^q < 2^K, \quad 200 K < 317 q, \quad 306 K < 485 q, \quad 2^K \cdot 2310000^q \le (3 \cdot 2310000 + 1)^q,$$
--
--   together with the per-rotation baseline bound $2786502 \cdot (2^K - 3^q) \le C(w.\operatorname{rotate}(d))$ for all $0 \le d < q$, the cycle denominator does not divide the affine constant:
--
--   $$(2^K - 3^q) \nmid C(w).$$
--
--   Then every positive periodic point $m \in \mathbb{N}$ of the Syracuse map is trivial: for all $m > 0$ and $p > 0$,
--
--   $$T^p(m) = m \implies m = 1.$$
--
--   This forward bridge theorem connects the open valuation-word frontier obligation `syracuse_primitive_word_affine_nondivisibility_ge_6956_with_rotated_baseline_2786502` (theorem f9fd04d9-1a91-4015-8f1e-d0e842ccf6be) directly to the global periodic-point exclusion for the Syracuse map, consolidating the short-period exclusion $q \le 6290$, the high-mean exclusion, the state-baseline budget filter, the sparse-period gap $q = 6291 \lor q \ge 6956$, and the exact period-$6291$ elimination into a single proved implication.
-- source:
--   Collatz cycle-exclusion frontier bridge packet (Mission 2f34a49f-2016-4de2-9662-fcd1cc96cc67), bridging leaf f9fd04d9-1a91-4015-8f1e-d0e842ccf6be to global Syracuse periodic-point triviality; helper lemmas adapted with attribution from accepted submissions 50d0932b, 8c51a6dd, and 26ec230a by FakeMink (090844a7-327d-477a-b08e-2937c520007f).

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_cycle_eq_one_of_primitive_word_ge_6956_rotated_baseline_2786502
    (hleaf : ∀ w : List ℕ,
      (∀ a ∈ w, 0 < a) →
      6956 ≤ w.length →
      (∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w) →
      3 ^ w.length < 2 ^ w.sum →
      200 * w.sum < 317 * w.length →
      306 * w.sum < 485 * w.length →
      (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤ (3 * 2310000 + 1 : ℕ) ^ w.length →
      (∀ d : ℕ, d < w.length →
        (2786502 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤ syracuseAffineConstant (w.rotate d)) →
      ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w)
    (m p : ℕ) (hm : 0 < m) (hp : 0 < p) (hcyc : syracuseStep^[p] m = m) :
    m = 1 := by sorry
