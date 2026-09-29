-- Prove2me | solution 1 for AttentionBudget.kstar_ge_of_bounded_ratio
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-08T19:47:32.382169+00:00
-- url     : https://prove2.me/submissions/c2b74638-7e64-45ec-9806-1bc759e60468
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Sol generated from Shared/AttentionBudgetKnee.lean
import Mathlib
import Definitions.Def_Shared_AttentionBudgetKnee
import Theorems.Thm_AttentionBudget_gate_le_retained_kstar
import Theorems.Thm_AttentionBudget_headMass_pos

/-!
# The attention-budget knee: context-stable versus context-sensitive key budgets

This file develops a formal, model-free theory of the object measured in the NET-65
experiment: the *retained attention mass* of a top-`k` truncation of a context of
length `n`, and the *knee* `k*(n)` — the smallest budget of retained keys whose mass
clears a fixed gate `τ`.

The empirical situation is a dichotomy.  For one family of models the knee grows with
context length (`{16, 20, 24}` over a rising context ladder), for another it is flat
(`{16, 16}`).  The theorems below identify exactly which structural property of the
attention weight profile separates the two regimes:

* **Geometric decay ⇒ bounded knee** (`kstar_uniformly_bounded_of_geometric_decay`).
  If the sorted weights obey `w (i+1) ≤ r * w i` with `r < 1`, then a single budget
  `K = K(r, τ)` satisfies `k*(n) ≤ K` for *every* context length `n`.  This is the
  "one 16-key budget covers every context" regime, and it makes the context
  sensitivity `k*(2n) - k*(n)` bounded (`ctxSens_bounded_of_geometric_decay`).
* **Bounded weight ratio (no spectral gap) ⇒ knee grows linearly**
  (`kstar_ge_of_bounded_ratio`): `k*(n) ≥ τ · n · c / M`.  For uniform weights this is
  sharp on both sides and the context sensitivity diverges
  (`ctxSens_uniform_unbounded`).

Together these give a genuine separation theorem, `context_sensitivity_dichotomy`:
boundedness of the attention budget across contexts is governed by the decay profile
of the sorted attention weights, and both regimes are non-empty.

Finally we formalise the *razor bracket* reasoning used to report `k* = 16`: pure
monotonicity of retained mass turns two measurements (a failure at `k = 12` and a pass
at `k = 16`) into the bracket `12 < k* ≤ 16` (`knee_bracket`, `net65_razor_bracket`),
and the strict increase of the reported sub-knee grid `4 < 6 < 8 < 12` is forced by
positivity of the weights alone (`subknee_grid_strictly_increasing`).

-- !-- Lab Notes -- !--
Hypothesizer (5 conjectures, ranked by expected impact):
 (H1) The knee is bounded across contexts iff the sorted attention profile has a
      geometric (spectral-gap) tail; parameter count is irrelevant.        [BOLD]
 (H2) Retained mass is monotone in `k` for every profile, so any two grid points
      bracket the knee — the "razor" is a theorem, not a statistical artefact.
 (H3) Gapless profiles (bounded ratio `w i ∈ [c, M]`) have knee `Θ(n)`, so the
      rising `{16, 20, 24}` chain is a gapless signature.
 (H4) There is a *universal* budget depending only on the decay ratio `r` and the
      gate `τ`, uniform in `n`: any `K` with `r ^ K / (1 - r) ≤ 1 - τ` works.
 (H5) A profile with a positive uniform floor cannot be context-stable: the floor
      alone forces linear growth of the knee.                               [BOLD]

Experimenter: H1–H5 are all formalised below and proved with zero sorries.
Measured NET-65 inputs (Qwen2.5-1.5B, ctx = 1024, gate 0.98):
  k        :   4        6        8       12       16
  retained : 0.9318   0.9532   0.9660   0.9759   (pass)
are used only as *hypotheses* of `net65_razor_bracket`, never as axioms.

Analyst: the informative failure is that flatness in the exact form
`k*(2n) = k*(n)` is **false** in general: for a geometric profile the normaliser
`headMass w n` still creeps upward with `n`, so `retained w n k` is weakly decreasing
in `n` and the knee can move by one step near a gate crossing.  The correct invariant
is *uniform boundedness*, not equality — a "needs a different definition" outcome,
and it is exactly what a two-point measurement `{16, 16}` can support.

Critic: no theorem here is vacuous.  `subknee_grid_strictly_increasing` shows the
sub-knee values are strictly increasing (the reported table is not a plateau);
`context_sensitivity_dichotomy` exhibits both regimes with explicit witnesses, so the
hypothesis classes are non-empty; and `retained_lt_one_of_lt` shows the gate is a real
constraint (retained mass is `< 1` strictly below the context length).
-/

open AttentionBudget

open Finset

/-! ## Retained mass, the knee, and context sensitivity -/





/-! ## Basic monotonicity theory -/


variable {w : ℕ → ℝ} (hw : ∀ i, 0 < w i)

include hw












/-! ## The knee: existence, characterisation, and the razor bracket -/


variable {w : ℕ → ℝ} {τ : ℝ} {n : ℕ} (hw : ∀ i, 0 < w i)

include hw











/-! ## Regime I: geometric decay gives a context-stable budget -/


variable {w : ℕ → ℝ} {r τ : ℝ}







/-! ## Regime II: no spectral gap forces a linearly growing budget -/


variable {w : ℕ → ℝ} {τ : ℝ} {n : ℕ}


/-! ### The uniform profile: both bounds are sharp -/







/-! ## The separation theorem -/



open AttentionBudget in
theorem solution(hw : ∀ i, 0 < w i) {c M : ℝ} (hc : 0 < c)
    (hlow : ∀ i, c ≤ w i) (hhigh : ∀ i, w i ≤ M) (hn : 0 < n) (hτ : τ ≤ 1) :
    τ * n * c / M ≤ (kstar w n τ : ℝ) := by
  have hM : 0 < M := lt_of_lt_of_le hc ((hlow 0).trans (hhigh 0))
  set k := kstar w n τ with hk
  have hpass : τ ≤ retained w n k := gate_le_retained_kstar hw hn hτ
  have hnum : headMass w (min k n) ≤ (k : ℝ) * M := by
    have h1 : headMass w (min k n) ≤ (min k n : ℝ) * M := by
      have := Finset.sum_le_sum (f := w) (g := fun _ => M)
        (s := Finset.range (min k n)) fun i _ => hhigh i
      simpa [headMass, mul_comm] using this
    have h2 : (min k n : ℝ) ≤ (k : ℝ) := by exact_mod_cast min_le_left k n
    nlinarith
  have hden : (n : ℝ) * c ≤ headMass w n := by
    have := Finset.sum_le_sum (f := fun _ => c) (g := w)
      (s := Finset.range n) fun i _ => hlow i
    simpa [headMass, mul_comm] using this
  have hdenpos : 0 < headMass w n := headMass_pos hw hn
  have hnc : 0 < (n : ℝ) * c := by positivity
  have : τ * headMass w n ≤ headMass w (min k n) := by
    rw [retained, le_div_iff₀ hdenpos] at hpass
    linarith
  have hτn : τ * ((n : ℝ) * c) ≤ (k : ℝ) * M := by
    rcases le_or_gt τ 0 with hτ0 | hτ0
    · have : τ * ((n : ℝ) * c) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hτ0 hnc.le
      have hkM : 0 ≤ (k : ℝ) * M := by positivity
      linarith
    · nlinarith
  rw [div_le_iff₀ hM]
  nlinarith
