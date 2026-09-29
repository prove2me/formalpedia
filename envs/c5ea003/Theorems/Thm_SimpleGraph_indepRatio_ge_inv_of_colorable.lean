-- Prove2me | Theorems.Thm_SimpleGraph_indepRatio_ge_inv_of_colorable
-- name    : SimpleGraph.indepRatio_ge_inv_of_colorable
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:31:38.98181+00:00
-- url     : https://prove2.me/theorems/c0390766-7a41-40fe-9288-dff724e45702
-- title:
--   Independence ratio lower bound from a colouring.
-- statement:
--   **Independence ratio lower bound from a colouring.**  If `G` is `k`-colourable and the
--   vertex set is nonempty, then `1/k ≤ i(G)`.  This inverts the pigeonhole bound `n ≤ k·α(G)`.
--
--   ```lean
--   theorem SimpleGraph.indepRatio_ge_inv_of_colorable{k : ℕ}
--       (hpos : 0 < Fintype.card V) (hC : G.Colorable k) :
--       (1 : ℚ) / k ≤ G.indepRatio := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/IndependenceRatioLowerBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/IndependenceRatioLowerBound.lean#L56

-- Thm stub generated from Novelty/IndependenceRatioLowerBound.lean
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic

/-!
# The independence ratio lower bound: `i(G) ≥ 1/χ(G)`

This file is the *positive* companion to `Catalog.Novelty.IndependenceRatioChromatic`.  That
file proved the reduction "small independence ratio ⇒ many colours"
(`i(G) < 1/4 ⇒ χ(G) > 4`).  Here we prove the exact converse engine: **a proper `k`-colouring
forces the independence ratio up**, i.e.

* `SimpleGraph.indepRatio_ge_inv_of_colorable` — if `G` is `k`-colourable and `V` is nonempty
  then `1/k ≤ i(G)`.
* `SimpleGraph.indepRatio_ge_inv_chromaticNumber` — unconditionally for a finite graph,
  `1/χ(G) ≤ i(G)` (the sharp reciprocal statement).
* `SimpleGraph.indepRatio_ge_quarter_of_colorable_four` — the on-topic corollary: any
  `4`-colourable graph has `i(G) ≥ 1/4`, so the independence ratio of a `4`-colourable graph
  *cannot fall below* `1/4`.

The point is that the "`1/4`" threshold in the Erdős / Matolcsi–Ruzsa–Varga–Zsámboki circle is
governed on *both* sides by the pigeonhole identity `n ≤ k·α(G)`: below `1/4` it forces
`χ > 4`, and conversely `χ ≤ 4` forces `i(G) ≥ 1/4`.  Thus the *Minimum Independence Ratio
Constraint* "`i(G) ≥ 1/4` for every finite unit-distance graph" is *equivalent* to the
statement "every finite unit-distance graph is (fractionally) `4`-colourable", pinpointing
exactly what a would-be counterexample must violate.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the "minimum independence ratio 1/4" claim is not an isolated
metric miracle; it is the reciprocal image of a colouring bound.  Bold form: `i(G) ≥ 1/k` is
*equivalent* to `k`-colourability up to the fractional relaxation, so the grand conjecture
`i(G) ≥ 1/4` for planar unit-distance graphs is the reciprocal of `χ_f(ℝ²) ≤ 4`.
Experiment (Experimenter): rearrange the catalog inequality `card_le_colors_mul_indepNum`
(`n ≤ k·α`) into `1/k ≤ α/n` by clearing denominators with `div_le_div_iff₀`; for the
chromatic-number form, use that a finite graph is `chromaticNumber.toNat`-colourable via
`colorable_of_chromaticNumber_ne_top`, with `chromaticNumber ≠ ⊤` coming from
`colorable_of_fintype`.
Analysis (Analyst): the integral bound `1/k ≤ i(G)` is tight exactly for balanced complete
multipartite graphs (all colour classes equal to a maximum independent set); the equilateral
triangle `K₃` realises `1/3 = 1/χ`.  So the reciprocal identity is sharp, not merely an
inequality.
Critique (Critic): `0 < card V` is load-bearing (the ratio is `0/0` otherwise); the `k = 0`
corner is harmless because `1/0 = 0 ≤ i(G)` in `ℚ`.  The theorem is not a definitional
identity — it genuinely inverts the pigeonhole partition bound.
Synthesis (PI): together with the reduction file this gives the full two-sided dictionary
`i(G) ≷ 1/4 ⇔ χ_f(G) ≶ 4`, isolating the *fractional 4-colourability of the plane* as the
precise content of the Minimum Independence Ratio Constraint.
-- !-- end Lab Notes -- !--
-/

open Finset

open SimpleGraph

variable {V : Type*} [Fintype V]
variable (G : SimpleGraph V)

theorem SimpleGraph.indepRatio_ge_inv_of_colorable{k : ℕ}
    (hpos : 0 < Fintype.card V) (hC : G.Colorable k) :
    (1 : ℚ) / k ≤ G.indepRatio := by sorry
