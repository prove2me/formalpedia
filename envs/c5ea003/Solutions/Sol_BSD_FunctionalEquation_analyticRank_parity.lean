-- Prove2me | solution 1 for BSD.FunctionalEquation.analyticRank_parity
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T03:41:48.009126+00:00
-- url     : https://prove2.me/submissions/157184aa-6205-499f-8c03-b4b7022bdf2e

-- Sol generated from Applications/BSD/FunctionalEquation.lean
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


/-- The leading-term factorization `L z = (z - s₀)^r • g z` with `g` analytic and
`g s₀ ≠ 0`, where `r = analyticRank L s₀`. -/
theorem analyticRank_factorization (L : ℂ → ℂ) (s₀ : ℂ) (hL : AnalyticAt ℂ L s₀)
    (hfin : analyticOrderAt L s₀ ≠ ⊤) :
    ∃ g : ℂ → ℂ, AnalyticAt ℂ g s₀ ∧ g s₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 s₀, L z = (z - s₀) ^ (analyticRank L s₀) • g z :=
  (hL.analyticOrderNatAt_eq_iff hfin (n := analyticRank L s₀)).mp rfl








/-! ### The conditional Parity Conjecture and the rational-point consequence

The remaining results chain the unconditional analytic parity theorem with the
*Birch–Swinnerton-Dyer rank equality* `analyticRank Λ 1 = r` (where `r` is the free
rank of the Mordell–Weil group `E(ℚ) ≅ ℤ^r × T`, `T` the finite torsion subgroup).
Under that single BSD hypothesis they yield:
  * the **Parity Conjecture** `(-1)^{algebraic rank} = w(E)`, and
  * the prediction that a curve with **root number `-1`** has *infinitely many*
    rational points.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): the parity theorem `(-1)^r = w` is invisible to the
  algebraic side until BSD identifies analytic and algebraic rank; once it does, the
  *algebraic* rank inherits the parity, and an odd rank is forced to be positive,
  hence the Mordell–Weil group `ℤ^r × T` is infinite.
Analysis (Analyst): the `r = 0` exclusion is automatic — `(-1)^0 = 1 ≠ -1` — so the
  root-number-`-1` hypothesis literally cannot coexist with a finite Mordell–Weil
  group under BSD; this is the cleanest falsifiable shadow of the parity conjecture.
Critique (Critic): `T` must be finite (else infinitude could come from torsion) and
  nonempty (the point at infinity guarantees this); both are honest facts about a real
  Mordell–Weil group. The model `modelL` (with `modelL_functional_equation`) realizes
  every `(r, w = (-1)^r)`, so the bridge is non-vacuous.
-/

/-
**Mordell–Weil infinitude criterion.**  A finitely generated abelian group of
shape `ℤ^r × T`, with `T` finite and nonempty, is infinite **iff** its free rank `r`
is positive.
-/

/-
**BSD ⟹ Parity Conjecture.**  Under the BSD rank equality `analyticRank Λ 1 = r`
and the functional equation with sign `w`, the *algebraic* rank `r` has the parity of
the root number: `(-1)^r = w`.
-/

/-
**Root number `-1` ⟹ infinitely many rational points (under BSD).**  If the
functional equation has sign `-1` and the BSD rank equality `analyticRank Λ 1 = r`
holds for the Mordell–Weil group `ℤ^r × T` (`T` finite nonempty), then `r` is odd,
hence positive, so `E(ℚ)` is infinite.
-/


open BSD.FunctionalEquation in
theorem solution(Λ : ℂ → ℂ) (w : ℂ) (hΛ : AnalyticAt ℂ Λ 1)
    (hfin : analyticOrderAt Λ 1 ≠ ⊤)
    (hfe : ∀ s, Λ (2 - s) = w * Λ s) :
    (-1 : ℂ) ^ (analyticRank Λ 1) = w := by
  -- By analyticRank_factorization Λ 1 hΛ hfin obtain g, hg : AnalyticAt ℂ g 1, hg0 : g 1 ≠ 0, heq : ∀ᶠ z in 𝓝 1, Λ z = (z - 1)^r • g z (smul = *).
  obtain ⟨g, hg, hg0, heq⟩ : ∃ g : ℂ → ℂ, AnalyticAt ℂ g 1 ∧ g 1 ≠ 0 ∧ ∀ᶠ z in 𝓝 1, Λ z = (z - 1) ^ (analyticRank Λ 1) * g z := by
    convert analyticRank_factorization Λ 1 hΛ hfin using 1;
  -- Since $g(1) \neq 0$, we can divide both sides of the equation by $g(1)$ to get $(-1)^r = w$.
  have h_div : ∀ᶠ z in nhdsWithin 1 {1}ᶜ, (-1 : ℂ) ^ (analyticRank Λ 1) * g (2 - z) = w * g z := by
    have h_eq : ∀ᶠ z in nhdsWithin 1 {1}ᶜ, Λ (2 - z) = (-1) ^ (analyticRank Λ 1) * (z - 1) ^ (analyticRank Λ 1) * g (2 - z) := by
      have h_eq : ∀ᶠ z in nhdsWithin 1 {1}ᶜ, Λ (2 - z) = (2 - z - 1) ^ (analyticRank Λ 1) * g (2 - z) := by
        have hT : Filter.Tendsto (fun z : ℂ => 2 - z) (nhds 1) (nhds 1) := by
          exact Continuous.tendsto' ( by continuity ) _ _ ( by norm_num );
        exact hT.eventually heq |> fun h => h.filter_mono nhdsWithin_le_nhds;
      filter_upwards [ h_eq ] with z hz using by rw [ hz ] ; rw [ ← mul_pow ] ; ring;
    filter_upwards [ h_eq, heq.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin ] with z hz₁ hz₂ hz₃ ; simp_all +decide [mul_comm];
    exact mul_left_cancel₀ ( pow_ne_zero ( analyticRank Λ 1 ) ( sub_ne_zero_of_ne hz₃ ) ) ( by linear_combination' hz₁.symm );
  -- Since $g$ is continuous at $1$, we can take the limit of both sides of the equation as $z$ approaches $1$.
  have h_lim : Filter.Tendsto (fun z => (-1 : ℂ) ^ (analyticRank Λ 1) * g (2 - z)) (nhdsWithin 1 {1}ᶜ) (nhds ((-1 : ℂ) ^ (analyticRank Λ 1) * g 1)) ∧ Filter.Tendsto (fun z => w * g z) (nhdsWithin 1 {1}ᶜ) (nhds (w * g 1)) := by
    constructor;
    · exact tendsto_const_nhds.mul ( hg.continuousAt.tendsto.comp ( tendsto_nhdsWithin_of_tendsto_nhds ( Continuous.tendsto' ( by continuity ) _ _ ( by norm_num ) ) ) );
    · exact tendsto_const_nhds.mul ( hg.continuousAt.continuousWithinAt );
  exact mul_left_cancel₀ hg0 <| by simpa using tendsto_nhds_unique h_lim.1 <| h_lim.2.congr' <| by filter_upwards [ h_div ] with z hz; aesop;
