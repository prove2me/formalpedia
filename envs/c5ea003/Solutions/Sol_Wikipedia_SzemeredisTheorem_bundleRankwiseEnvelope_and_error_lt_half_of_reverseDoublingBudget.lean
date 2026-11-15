-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.bundleRankwiseEnvelope_and_error_lt_half_of_reverseDoublingBudget
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:35:31.464114+00:00
-- url     : https://prove2.me/submissions/9b033f05-9a69-4478-a60a-9bfb6f178f66

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_RankwiseBundleEnvelopeSelection
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Theorems.Thm_Wikipedia_SzemeredisTheorem_bundleRankwiseEnvelopeError_isEnvelope
import Theorems.Thm_Wikipedia_SzemeredisTheorem_bundleRankwiseEnvelopeError_le_finiteBudget
import Theorems.Thm_Wikipedia_SzemeredisTheorem_bundleRankwiseEnvelopeError_monotone_card

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Rankwise numerical envelopes for bundle counting

The generalized bundle-counting recurrence permits the density and
localized-defect parameters to depend on the rank.  This file supplies a
direct numerical envelope for those rankwise parameters.  Its density floor
is the prefix minimum of the rankwise densities, so no global density lower
bound is needed.

The row constructor takes a maximum with the preceding-order row.  This
makes monotonicity in bundle order automatic even when consecutive ranks use
unrelated parameters; its other branch is equality in the one-edge counting
recurrence.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology

/-! ## Prefix density floors -/





@[simp]
theorem bundleRankwiseDensityFloor_succ (α : ℕ → ℝ) (d : ℕ) :
    bundleRankwiseDensityFloor α (d + 1) =
      min (bundleRankwiseDensityFloor α d) (α (d + 1)) :=
  rfl

/-- A positive rankwise density schedule has positive prefix floors. -/
theorem bundleRankwiseDensityFloor_pos
    {α : ℕ → ℝ} (hα : ∀ d, 0 < α d) :
    ∀ d, 0 < bundleRankwiseDensityFloor α d := by
  intro d
  induction d with
  | zero => simpa using hα 0
  | succ d ih =>
      simpa using lt_min ih (hα (d + 1))





/-! ## The rankwise recurrence -/







@[simp]
theorem bundleRankwiseNextRow_zero
    (α β μ : ℕ → ℝ) (τ : ℝ) (d : ℕ) (lower : ℕ → ℝ) :
    bundleRankwiseNextRow α β μ τ d lower 0 = 0 :=
  rfl



@[simp]
theorem bundleRankwiseEnvelopeError_zero_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ 0 n = 0 :=
  rfl

@[simp]
theorem bundleRankwiseEnvelopeError_succ_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ (d + 1) n =
      bundleRankwiseNextRow α β μ τ d
        (bundleRankwiseEnvelopeError α β μ τ d) n :=
  rfl

/-! ## Positivity and monotonicity -/















/-! ## The generalized-counting interface -/



/-! ## Vanishing and continuous rankwise parameter paths -/









/-! ## Density-scaled finite-horizon selection -/



















/-! ## Explicit finite-horizon sufficient bounds -/



theorem bundleReverseDoublingHorizon_two_mul_succ
    {rankBound edgeBound d : ℕ} (hd : d < rankBound) :
    2 * bundleReverseDoublingHorizon rankBound edgeBound (d + 1) =
      bundleReverseDoublingHorizon rankBound edgeBound d := by
  have hsub : rankBound - d = rankBound - (d + 1) + 1 := by
    omega
  simp only [bundleReverseDoublingHorizon, hsub, pow_succ]
  ring

theorem bundleReverseDoublingHorizon_le_zero
    (rankBound edgeBound d : ℕ) :
    bundleReverseDoublingHorizon rankBound edgeBound d ≤
      bundleReverseDoublingHorizon rankBound edgeBound 0 := by
  unfold bundleReverseDoublingHorizon
  apply Nat.mul_le_mul_left
  exact (pow_right_monotone (by norm_num : (1 : ℕ) ≤ 2))
    (Nat.sub_le rankBound d)





/-- Specialization of the finite-budget theorem to the canonical
reverse-doubling horizons. -/
theorem bundleRankwiseEnvelopeError_le_reverseDoublingBudget
    {α β μ : ℕ → ℝ} {τ η B : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hβ : ∀ d, 0 ≤ β d)
    (hμ : ∀ d, 0 ≤ μ d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound edgeBound : ℕ)
    (hcap :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η ≤ B)
    (hdefect : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    bundleRankwiseEnvelopeError α β μ τ rankBound (edgeBound + 1) ≤
      (rankBound : ℝ) *
        (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η := by
  apply bundleRankwiseEnvelopeError_le_finiteBudget hα hβ hμ hτ hη
    rankBound (bundleReverseDoublingHorizon rankBound edgeBound)
    (fun d hd => (bundleReverseDoublingHorizon_two_mul_succ hd).le)
    (fun d _hd => bundleReverseDoublingHorizon_le_zero rankBound edgeBound d)
    hcap hdefect huniform rankBound le_rfl (edgeBound + 1)
  simp [bundleReverseDoublingHorizon]



end Wikipedia.SzemeredisTheorem

end
/-!
# Rankwise numerical envelopes for bundle counting

The generalized bundle-counting recurrence permits the density and
localized-defect parameters to depend on the rank.  This file supplies a
direct numerical envelope for those rankwise parameters.  Its density floor
is the prefix minimum of the rankwise densities, so no global density lower
bound is needed.

The row constructor takes a maximum with the preceding-order row.  This
makes monotonicity in bundle order automatic even when consecutive ranks use
unrelated parameters; its other branch is equality in the one-edge counting
recurrence.
-/
open Wikipedia.SzemeredisTheorem
open Filter Topology
/-! ## Prefix density floors -/
/-! ## The rankwise recurrence -/
/-! ## Positivity and monotonicity -/
/-! ## The generalized-counting interface -/
/-! ## Vanishing and continuous rankwise parameter paths -/
/-! ## Density-scaled finite-horizon selection -/
/-! ## Explicit finite-horizon sufficient bounds -/

open Wikipedia.SzemeredisTheorem in
/-- A ready-to-use half-error criterion with prefix density floors.

The cap `1` makes every lower correction factor at most `2`.  The defect
conditions remain rank-local, while the uniform conditions use only the
prefix floor.  The conclusion packages both the global counting-envelope
interface and the finite error estimate needed for positivity. -/
theorem solution
    {α β : ℕ → ℝ} {τ η : ℝ}
    (hα : ∀ d, 0 < α d) (hα_one : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound edgeBound : ℕ)
    (hcap :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η ≤ 1)
    (hfinal :
      (rankBound : ℝ) *
          (bundleReverseDoublingHorizon rankBound edgeBound 0 : ℝ) * η < 1 / 2)
    (hdefect : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + (1 : ℝ)) * (1 + (1 : ℝ))) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n,
      n < bundleReverseDoublingHorizon rankBound edgeBound (d + 1) →
      τ /
          (bundleRankwiseDensityFloor α (d + 1)) ^ (n + 1) ≤
        η / 2) :
    IsBundleCountingEnvelope α β
        (bundleRankwiseDensityFloor α) τ
        (bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ) ∧
      bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ rankBound edgeBound < 1 / 2 := by
  have hμ : ∀ d, 0 ≤ bundleRankwiseDensityFloor α d :=
    fun d => (bundleRankwiseDensityFloor_pos hα d).le
  have hbound :=
    bundleRankwiseEnvelopeError_le_reverseDoublingBudget
      (fun d => (hα d).le) hβ hμ hτ hη rankBound edgeBound
      hcap hdefect huniform
  have hcard :
      bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ rankBound edgeBound ≤
        bundleRankwiseEnvelopeError α β
          (bundleRankwiseDensityFloor α) τ rankBound (edgeBound + 1) :=
    (bundleRankwiseEnvelopeError_monotone_card
      (fun d => (hα d).le) hμ hτ rankBound) (Nat.le_succ edgeBound)
  exact ⟨bundleRankwiseEnvelopeError_isEnvelope hα hα_one hβ hτ,
    (hcard.trans hbound).trans_lt hfinal⟩
