-- Prove2me | solution 1 for SocialCredit.monotone_credit_has_fixedPoint
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:18:09.323794+00:00
-- url     : https://prove2.me/submissions/0c2b08e9-fe1b-4dc6-9af3-dfbb0c807d82

-- Sol generated from Applications/SocialCredit/FixedPoint.lean
import Mathlib
import Definitions.Def_Applications_SocialCredit_FixedPoint

/-!
# Social Credit Scores as Fixed-Point Attractors

We model a **social credit system** as a map assigning to each member of a
population a *score* living in a totally ordered set (here the real line `ℝ`,
the prototypical complete, totally ordered value space).  Two structural
phenomena are made precise.

* **Extremal members.** On a compact population a continuous scoring map always
  realises a highest- and a lowest-scoring member (`credit_attains_max`,
  `credit_attains_min`).  This is the topological reason a social credit system
  always has identifiable "best" and "worst" ranked individuals.

* **Attractors of the update dynamics.** Credit is not static: each round a
  member's score is revised by a *reward* `c` plus a *damped memory* `k · (old
  score)` of the previous value.  When the damping factor satisfies
  `0 ≤ k < 1` the update map is a contraction, and every starting score
  converges to a single equilibrium `c / (1 - k)`, independent of the initial
  condition (`creditIterate_tendsto`).  The equilibrium is the unique fixed
  point (`creditEquilibrium_unique`).

* **Order-theoretic attractors.** Even without any contraction or continuity
  assumption, a *monotone* credit map on the score interval `[0,1]` must have an
  equilibrium score (`monotone_credit_has_fixedPoint`): a Knaster–Tarski fixed
  point obtained as the supremum of the sub-fixed points.
-/

open Filter Topology

open SocialCredit

/-! ## Extremal members of a compact population -/

/-
A continuous credit map on a nonempty compact population attains a maximum:
there is a highest-scoring member.
-/

/-
A continuous credit map on a nonempty compact population attains a minimum:
there is a lowest-scoring member.
-/

/-! ## The affine credit-update dynamics -/




/-
The equilibrium score is a fixed point of the update map.
-/

/-
Closed form for the score after `n` rounds.
-/

/-
**Fixed-point attractor.**  With damping `0 ≤ k < 1`, every starting score
converges to the equilibrium, independently of the initial condition.
-/

/-
The equilibrium is the *unique* fixed point of the update map (for `k ≠ 1`).
-/

/-! ## Order-theoretic attractor: Knaster–Tarski on the score interval -/

/-
**Knaster–Tarski for credit scores.**  A monotone credit map that keeps
scores inside `[0,1]` always has an equilibrium score in `[0,1]`, with no
continuity or contraction hypothesis.
-/


open SocialCredit in
theorem solution(f : ℝ → ℝ) (hmono : Monotone f)
    (hmaps : ∀ x ∈ Set.Icc (0:ℝ) 1, f x ∈ Set.Icc (0:ℝ) 1) :
    ∃ x ∈ Set.Icc (0:ℝ) 1, f x = x := by
  by_contra! h_contra;
  -- Let $S := {x : ℝ | x ∈ Set.Icc (0:ℝ) 1 ∧ x ≤ f x}$.
  set S := {x : ℝ | x ∈ Set.Icc (0:ℝ) 1 ∧ x ≤ f x} with hS_def

  -- Note $0 ∈ S$: $0 ∈ Icc 0 1$, and $f 0 ∈ Icc 0 1$ (from `hmaps`) gives $0 ≤ f 0$.
  have h0_in_S : (0 : ℝ) ∈ S := by
    exact ⟨ by norm_num, hmaps 0 ( by norm_num ) |>.1 ⟩

  -- So `S` is nonempty.
  have hS_nonempty : S.Nonempty := by
    exact ⟨ _, h0_in_S ⟩

  -- `S` is bounded above by `1` (every element is in `Icc 0 1`).
  have hS_bdd_above : BddAbove S := by
    exact ⟨ 1, fun x hx => hx.1.2 ⟩

  -- Let `s := sSup S`. Then `0 ≤ s` (since `0 ∈ S` and `le_csSup`) and `s ≤ 1` (since `1` is an upper bound and `csSup_le`).
  set s := sSup S with hs_def
  have hs_bounds : s ∈ Set.Icc (0:ℝ) 1 := by
    exact ⟨ le_trans h0_in_S.1.1 <| le_csSup hS_bdd_above h0_in_S, csSup_le hS_nonempty fun x hx => hx.1.2 ⟩;
  -- Show `s ≤ f s`: For any `x ∈ S`, `x ≤ s` (`le_csSup`), so `f x ≤ f s` by `hmono`; combined with `x ≤ f x` gives `x ≤ f s`. Thus `f s` is an upper bound of `S`, so `s = sSup S ≤ f s` by `csSup_le` (S nonempty).
  have hs_le_fs : s ≤ f s := by
    exact csSup_le hS_nonempty fun x hx => le_trans hx.2 <| hmono <| le_csSup hS_bdd_above hx;
  exact h_contra s hs_bounds <| le_antisymm ( by exact le_csSup hS_bdd_above ⟨ hmaps s hs_bounds, by linarith [ hmono hs_le_fs ] ⟩ ) hs_le_fs
