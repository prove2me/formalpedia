-- Prove2me | Theorems.Thm_syracuse_primitive_word_ge_6956_rotated_baseline_2786502_of_no_cycle
-- name    : syracuse_primitive_word_ge_6956_rotated_baseline_2786502_of_no_cycle
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-07T13:27:06.820013+00:00
-- url     : https://prove2.me/theorems/522d9d06-9074-4b4f-9111-8afc0644fa2a
-- title:
--   Derivation of the period-6956 rotated-baseline word frontier from the absence of long Syracuse cycles
-- statement:
--   Let $T : \mathbb{N} \to \mathbb{N}$ denote the accelerated Syracuse map $T(n) = (3n + 1)/2^{\nu_2(3n + 1)}$, and let $C(w) = \operatorname{syracuseAffineConstant}(w)$ denote the canonical Syracuse affine constant of a finite valuation word $w = (e_0, \ldots, e_{p-1})$ of length $p = \operatorname{length}(w)$ and sum $K = \sum_{i=0}^{p-1} e_i$. Assume that no nontrivial positive periodic point of $T$ has minimal period at least $6956$:
--
--   $$\forall m, p \in \mathbb{N}, \quad \bigl(m > 0 \land p \ge 6956 \land \operatorname{minimalPeriod}_T(m) = p\bigr) \implies m = 1.$$
--
--   Then for every positive valuation word $w$ ($e_i > 0$) of length $p \ge 6956$ that is primitive under proper cyclic rotations ($w.\operatorname{rotate}(d) \ne w$ for $0 < d < p$) and satisfies $3^p < 2^K$, $200 K < 317 p$, $306 K < 485 p$, $2^K \cdot 2310000^p \le (3 \cdot 2310000 + 1)^p$, and $2786502 \cdot (2^K - 3^p) \le C(w.\operatorname{rotate}(d))$ for all $0 \le d < p$, the cycle denominator does not divide the affine constant:
--
--   $$(2^K - 3^p) \nmid C(w).$$
--
--   This reverse bridge theorem proves that the open valuation-word frontier obligation `syracuse_primitive_word_affine_nondivisibility_ge_6956_with_rotated_baseline_2786502` (theorem f9fd04d9-1a91-4015-8f1e-d0e842ccf6be) introduces no unprovable artifacts beyond the genuine dynamical question of excluding nontrivial Syracuse cycles of minimal period $p \ge 6956$.
-- source:
--   Collatz cycle-exclusion frontier bridge packet (Mission 2f34a49f-2016-4de2-9662-fcd1cc96cc67), proving the converse implication from minimal-period cycle exclusion to leaf f9fd04d9-1a91-4015-8f1e-d0e842ccf6be via 78b082d4-594c-4179-8e50-8e372a26c563; adapted with attribution from 9675ddf1 and 50d0932b by FakeMink (090844a7-327d-477a-b08e-2937c520007f).

import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Tactic.Ring
import Definitions.Def_syracuseStep
import Definitions.Def_syracuseOffsetMod

set_option autoImplicit false

theorem syracuse_primitive_word_ge_6956_rotated_baseline_2786502_of_no_cycle
    (hnocycle : ∀ m p : ℕ, 0 < m → 6956 ≤ p →
      Function.minimalPeriod syracuseStep m = p → m = 1)
    (w : List ℕ)
    (hpositive : ∀ a ∈ w, 0 < a)
    (hlength : 6956 ≤ w.length)
    (hprimitive : ∀ d : ℕ, 0 < d → d < w.length → w.rotate d ≠ w)
    (hgap : 3 ^ w.length < 2 ^ w.sum)
    (hlow : 200 * w.sum < 317 * w.length)
    (hlowSharp : 306 * w.sum < 485 * w.length)
    (hbaselineBudget : (2 : ℕ) ^ w.sum * (2310000 : ℕ) ^ w.length ≤
      (3 * 2310000 + 1 : ℕ) ^ w.length)
    (hrotatedBaseline : ∀ d : ℕ, d < w.length →
      (2786502 : ℕ) * (2 ^ w.sum - 3 ^ w.length) ≤
        syracuseAffineConstant (w.rotate d)) :
    ¬(2 ^ w.sum - 3 ^ w.length) ∣ syracuseAffineConstant w := by sorry
