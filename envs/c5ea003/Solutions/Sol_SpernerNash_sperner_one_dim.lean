-- Prove2me | solution 1 for SpernerNash.sperner_one_dim
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:58:01.151221+00:00
-- url     : https://prove2.me/submissions/39a995c3-bf15-44fb-bc0b-723484cf47a7

-- Sol generated from Geometry/GameTheory/SpernerNash.lean
import Mathlib
import Definitions.Def_Geometry_GameTheory_SpernerNash
/-
# Sperner's Lemma Directly Yields Approximate Nash Equilibria

This module proves that **Sperner's lemma** directly yields approximate Nash
equilibria for finite two-player games, *without* invoking any topological
fixed-point theorem (Brouwer / Kakutani) and without invoking Nash's existence
theorem.

The development is organized as:

* Mixed strategies as the standard simplex `stdSimplex ℝ A`.
* Expected payoffs `payA`, `payB`, pure-strategy payoffs, best-response value
  and regret.
* Elementary analytic facts: bilinearity / Lipschitz bounds for the expected
  payoff (with explicit constants in terms of the payoff bound `L`), and the
  key *regret-from-support* lemma.
* The best-response Sperner labeling and the proof that the labeled pure
  strategy is genuinely a best response (properness of the labeling).
* The combinatorial core (`spernerCore`): a fully-labeled cell of a fine
  triangulation produces a profile with approximate complementary slackness.
  This is exactly the place where Sperner's lemma is applied; it is the only
  classical combinatorial input and uses *no* fixed-point theorem.
* The main theorem `sperner_yields_approx_nash`, deduced analytically from
  `spernerCore` and the regret-from-support lemma.

## Main result

`sperner_yields_approx_nash`: for payoffs bounded by `L`, and every `δ > 0`,
there is a mixed-strategy profile whose regret for both players is at most
`C * L * δ`, where `C` depends only on `|A|` and `|B|`.
-/


open scoped BigOperators
open Finset

open SpernerNash

variable {A B : Type*}

/-! ## Expected payoffs, best response and regret -/









/-! ## Elementary identities -/



/-! ## Best-response value: basic facts -/





/-! ## Lipschitz bounds for the expected payoff

These are the elementary real-analysis facts replacing any appeal to continuity
machinery: the pure-strategy payoff is `L`-Lipschitz in the opponent's mixed
strategy with respect to the `ℓ¹` distance. -/



/-! ## The regret-from-support lemma

This is the analytic heart of the extraction step.  If a mixed strategy `σ₁`
only places weight on pure strategies whose payoff against `σ₂` is within `ε` of
the best response value, then the regret of `σ₁` against `σ₂` is at most `ε`.
This is exactly the *approximate complementary slackness* condition, and is what
a fully-labeled Sperner cell provides geometrically. -/



/-! ## The best-response Sperner labeling

The Sperner labeling assigns to each profile a pure strategy that is a best
response (with tie-breaking by smallest index, realized here through `Finset`
minima).  The properness statement is that the labeled pure strategy is indeed a
best response, i.e. its payoff equals the best-response value.  This is the
"valid Sperner labeling" condition: each vertex receives a label corresponding
to an active best-response coordinate. -/





/-! ## Sperner's lemma: the one-dimensional base case

Sperner's lemma in dimension one is the elementary combinatorial seed of the
whole theory (the discrete intermediate value theorem): a `{0,1}`-labeling of a
path whose endpoints carry the two different labels must contain an adjacent
`0 → 1` change.  It is proved here purely combinatorially, with no fixed-point
input, and is the base case for the induction underlying the
general-dimensional Sperner lemma used in `spernerCore`. -/

/-!
## Deferred general-dimensional extension

The original version of this file ended with two declarations depending on a
full triangulation proof of general-dimensional Sperner's lemma for a product of
simplices. That development was not supplied, and its central declaration had
an omitted proof. To keep the catalog sound and every active declaration fully
proved, those two unfinished declarations are preserved below as commented
research material rather than exported as theorems. The proved API above ends
with `sperner_one_dim`.
-/

/-
/-! ## The combinatorial core: Sperner's lemma applied to the best-response labeling

This is the single step that uses Sperner's lemma.  Triangulate the product of
the two strategy simplices `Δ(A) × Δ(B)` (which is homeomorphic to a simplex of
dimension `|A| + |B| - 2`) with mesh `δ`, and label each vertex by the
best-response labeling above.  By Sperner's lemma there is a fully-labeled cell;
its barycenter `(σ₁, σ₂)` satisfies the *approximate complementary slackness*
condition: every pure strategy in the support of `σ₁` is within `C * L * δ` of a
best response to `σ₂`, and symmetrically for `σ₂`.

This step relies only on Sperner's lemma and the elementary Lipschitz estimates
above; it uses **no** fixed-point theorem (Brouwer / Kakutani) and **not** Nash's
theorem.  It is the combinatorial input from which the main theorem follows
analytically (see `sperner_yields_approx_nash`).

IMPLEMENTATION STATUS.  This proposed lemma requires
the full general-dimensional Sperner's lemma together with a mesh-`δ`
triangulation of the product polytope `Δ(A) × Δ(B)`, neither of which is
available in Mathlib; formalizing them is a substantial independent development.
The active declarations preceding this research note — the analytic infrastructure,
the regret-from-support reduction, the best-response labeling and its properness,
and the one-dimensional Sperner base case — are fully proved. -/
theorem spernerCore [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (pA pB : A → B → ℝ) (L : ℝ) (hL : ∀ a b, |pA a b| ≤ L ∧ |pB a b| ≤ L) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ →
      ∃ σ₁ ∈ stdSimplex ℝ A, ∃ σ₂ ∈ stdSimplex ℝ B,
        (∀ a, 0 < σ₁ a → brValA pA σ₂ - purePayA pA a σ₂ ≤ C * L * δ) ∧
        (∀ b, 0 < σ₂ b → brValB pB σ₁ - purePayB pB b σ₁ ≤ C * L * δ) := by
  -- The general-dimensional triangulation proof was not supplied.

/-! ## Main theorem -/

/-- **Sperner's lemma yields approximate Nash equilibria.**

For a finite two-player game with payoffs bounded by `L`, and for every `δ > 0`,
there is a mixed-strategy profile `(σ₁, σ₂)` whose regret for both players is at
most `C * L * δ`, where the constant `C` depends only on `|A|` and `|B|`.

The proof goes entirely through Sperner's lemma (`spernerCore`) and elementary
real analysis; it does **not** use Brouwer's or Kakutani's fixed-point theorem,
nor Nash's existence theorem. -/
theorem sperner_yields_approx_nash {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (pA pB : A → B → ℝ) (L : ℝ)
    (hL : ∀ a b, |pA a b| ≤ L ∧ |pB a b| ≤ L) :
    ∃ C : ℝ, ∀ δ : ℝ, 0 < δ →
      ∃ σ₁ ∈ stdSimplex ℝ A, ∃ σ₂ ∈ stdSimplex ℝ B,
        regretA pA σ₁ σ₂ ≤ C * L * δ ∧ regretB pB σ₁ σ₂ ≤ C * L * δ := by
  obtain ⟨C, hC⟩ := spernerCore pA pB L hL
  refine ⟨C, fun δ hδ => ?_⟩
  obtain ⟨σ₁, hσ₁, σ₂, hσ₂, hsupp₁, hsupp₂⟩ := hC δ hδ
  refine ⟨σ₁, hσ₁, σ₂, hσ₂, ?_, ?_⟩
  · exact regretA_le_of_support pA σ₁ σ₂ (C * L * δ) hσ₁ hsupp₁
  · exact regretB_le_of_support pB σ₁ σ₂ (C * L * δ) hσ₂ hsupp₂

-/


open SpernerNash in
theorem solution(n : ℕ) (c : ℕ → Fin 2) (h0 : c 0 = 0) (hn : c n = 1) :
    ∃ i, i < n ∧ c i = 0 ∧ c (i + 1) = 1 := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ i, i ≤ n → c i = 0 := by
    intro i
    induction i with
    | zero => intro _; exact h0
    | succ k ih =>
      intro hk
      have hkn : k < n := Nat.lt_of_succ_le hk
      have hck : c k = 0 := ih (le_of_lt hkn)
      by_contra hne
      have h1 : c (k + 1) = 1 := by omega
      exact absurd h1 (hcon k hkn hck)
  have hcn := key n (le_refl n)
  rw [hn] at hcn
  exact absurd hcn (by decide)
