-- Prove2me | Theorems.Thm_BSD_FunctionalEquation_analyticRank_parity
-- name    : BSD.FunctionalEquation.analyticRank_parity
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:21:03.170993+00:00
-- url     : https://prove2.me/theorems/065f936c-ad1c-4e9f-93d2-c46ff4da5e2a
-- title:
--   Parity theorem (analytic core).
-- statement:
--   **Parity theorem (analytic core).**  Let `Λ` be analytic at the central point
--   `s = 1`, with finite order of vanishing there (it is not locally zero), and suppose it
--   satisfies the functional-equation symmetry `Λ(2 - s) = w · Λ(s)`.  Then the sign is
--   determined by the parity of the analytic rank:
--
--     `(-1)^{analyticRank Λ 1} = w`.
--
--   In particular `w = ±1`.  This is the unconditional analytic mechanism underlying the
--   Parity Conjecture.
--
--   ```lean
--   theorem BSD.FunctionalEquation.analyticRank_parity(Λ : ℂ → ℂ) (w : ℂ) (hΛ : AnalyticAt ℂ Λ 1)
--       (hfin : analyticOrderAt Λ 1 ≠ ⊤)
--       (hfe : ∀ s, Λ (2 - s) = w * Λ s) :
--       (-1 : ℂ) ^ (analyticRank Λ 1) = w := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/BSD/FunctionalEquation.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/BSD/FunctionalEquation.lean#L86

-- Thm stub generated from Applications/BSD/FunctionalEquation.lean
import Mathlib
import Definitions.Def_Applications_BSD_FunctionalEquation
/-
Copyright (c) 2025 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# BSD Research Cycle — The Functional Equation, the Sign, and the Parity of the Rank

The completed Hasse–Weil L-function `Λ(E, s) = N^{s/2} (2π)^{-s} Γ(s) L(E, s)` of an
elliptic curve `E / ℚ` satisfies a functional equation relating `s` to `2 - s`:

  `Λ(E, 2 - s) = w(E) · Λ(E, s)`,    `w(E) = ±1`,

where the *sign* `w(E)` is the **global root number**.  The **Parity Conjecture**
asserts that the analytic rank has the parity prescribed by the root number,
`(-1)^{rank_an(E)} = w(E)`, and — through BSD — that the *algebraic* (Mordell–Weil)
rank has the same parity.

This file proves the analytic mechanism behind the parity conjecture *unconditionally*
at the level of orders of vanishing: any function analytic at the central point `s = 1`
and satisfying the functional-equation symmetry `Λ(2 - s) = w · Λ(s)` has

  `(-1)^{ord_{s=1} Λ} = w`.

It then derives the qualitative corollaries (sign `-1` forces central vanishing; the
rank is even iff the sign is `+1`) and verifies the framework is non-vacuous by
exhibiting the model L-function `(s-1)^r · c` as a genuine solution of the functional
equation with sign `(-1)^r`.

This module mirrors the analytic-rank definition of `BSD.AnalyticRank` (kept self
contained here so the proof search has a single-file context) and is the analytic
companion to `RankBridge.lean`; the conditional parity-of-rank consequence is in
`ParityBridge.lean`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the parity statement `(-1)^r = w` is *not* analytic
  black magic — it is forced by Taylor symmetry.  If `Λ(1 + z) = Σ cₖ zᵏ`, the
  functional equation `Λ(1 - z) = w Λ(1 + z)` reads `Σ cₖ (-z)ᵏ = w Σ cₖ zᵏ`, hence
  `(-1)ᵏ cₖ = w cₖ` for every `k`; on the lowest nonvanishing coefficient `c_r` this
  is exactly `(-1)^r = w`.
Experiment (Experimenter): rather than manipulate Taylor coefficients, reuse the
  leading-term factorization `Λ z = (z-1)^r • g z` with `g 1 ≠ 0` (`analyticRank_factorization`),
  plug it into the functional equation on a punctured neighbourhood of `1`, cancel
  `(z-1)^r`, and pass to the limit `z → 1`.
Analysis (Analyst): the cancellation is legal only off the central point, so the
  identity `(-1)^r g(2-z) = w g(z)` lives on `𝓝[≠] 1`; continuity of both sides
  (analytic ⇒ continuous) and `NeBot (𝓝[≠] 1)` upgrade it to equality *at* `1`,
  where `g 1 ≠ 0` cancels to leave `(-1)^r = w`.
Critique (Critic): is the hypothesis satisfiable, or have we proved a statement
  about the empty set?  `modelL_functional_equation` shows the rank-`r` model
  `(s-1)^r · c` solves the functional equation with sign `(-1)^r`, so every sign and
  every rank is realised — the parity theorem is consistent and non-vacuous.
Synthesis (PI): `analyticRank_parity` is the unconditional analytic core of the
  parity conjecture; chained with the BSD rank equality (see `ParityBridge.lean`) it
  yields `(-1)^{algebraic rank} = w` and the "root number `-1` ⟹ infinitely many
  rational points" prediction.
-/

open BSD.FunctionalEquation

open Filter Topology

theorem BSD.FunctionalEquation.analyticRank_parity(Λ : ℂ → ℂ) (w : ℂ) (hΛ : AnalyticAt ℂ Λ 1)
    (hfin : analyticOrderAt Λ 1 ≠ ⊤)
    (hfe : ∀ s, Λ (2 - s) = w * Λ s) :
    (-1 : ℂ) ^ (analyticRank Λ 1) = w := by sorry
