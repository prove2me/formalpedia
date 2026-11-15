-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.bundleRankwiseEnvelopeError_isEnvelope
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:27:05.495418+00:00
-- url     : https://prove2.me/submissions/20a4d21c-7791-4c51-8c87-440fdac9465f

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_bundleRankwiseDensityFloor_le
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
theorem bundleRankwiseNextRow_succ
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) (lower : ℕ → ℝ) :
    bundleRankwiseNextRow α β μ τ d lower (n + 1) =
      max (lower (n + 1))
        (bundleRankwiseNextRow α β μ τ d lower n +
          bundleRankwiseStepIncrement α β μ τ lower d n) :=
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

theorem bundleRankwiseStepIncrement_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) (lower : ℕ → ℝ) (d n : ℕ) :
    0 ≤ bundleRankwiseStepIncrement α β μ τ lower d n := by
  unfold bundleRankwiseStepIncrement
  exact add_nonneg
    (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg (hα _) _))
    (div_nonneg hτ (pow_nonneg (hμ _) _))

theorem bundleRankwiseNextRow_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) (d : ℕ) (lower : ℕ → ℝ) :
    ∀ n, 0 ≤ bundleRankwiseNextRow α β μ τ d lower n := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      rw [bundleRankwiseNextRow_succ]
      exact le_max_of_le_right
        (add_nonneg ih
          (bundleRankwiseStepIncrement_nonneg hα hμ hτ lower d n))

theorem bundleRankwiseEnvelopeError_nonneg
    {α β μ : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hμ : ∀ d, 0 ≤ μ d)
    (hτ : 0 ≤ τ) :
    ∀ d n, 0 ≤ bundleRankwiseEnvelopeError α β μ τ d n := by
  intro d
  induction d with
  | zero =>
      intro n
      simp
  | succ d _ih =>
      intro n
      rw [bundleRankwiseEnvelopeError_succ_order]
      exact bundleRankwiseNextRow_nonneg hα hμ hτ d _ n

@[simp]
theorem bundleRankwiseEnvelopeError_zero_card
    (α β μ : ℕ → ℝ) (τ : ℝ) :
    ∀ d, bundleRankwiseEnvelopeError α β μ τ d 0 = 0 := by
  intro d
  cases d <;> simp



/-- The maximum in the row constructor makes the error monotone in rank. -/
theorem bundleRankwiseEnvelopeError_le_succ_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (d n : ℕ) :
    bundleRankwiseEnvelopeError α β μ τ d n ≤
      bundleRankwiseEnvelopeError α β μ τ (d + 1) n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [bundleRankwiseEnvelopeError_succ_order,
        bundleRankwiseNextRow_succ]
      exact le_max_left _ _

theorem bundleRankwiseEnvelopeError_monotone_order
    (α β μ : ℕ → ℝ) (τ : ℝ) (n : ℕ) :
    Monotone (fun d => bundleRankwiseEnvelopeError α β μ τ d n) := by
  apply monotone_nat_of_le_succ
  exact fun d => bundleRankwiseEnvelopeError_le_succ_order α β μ τ d n

/-! ## The generalized-counting interface -/



/-! ## Vanishing and continuous rankwise parameter paths -/









/-! ## Density-scaled finite-horizon selection -/



















/-! ## Explicit finite-horizon sufficient bounds -/















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

open Wikipedia.SzemeredisTheorem in
/-- The rankwise equality/max schedule is a counting envelope with the
prefix-minimum density floor. -/
theorem solution
    {α β : ℕ → ℝ} {τ : ℝ}
    (hα : ∀ d, 0 < α d) (hα_one : ∀ d, α d ≤ 1)
    (hβ : ∀ d, 0 ≤ β d) (hτ : 0 ≤ τ) :
    IsBundleCountingEnvelope α β
      (bundleRankwiseDensityFloor α) τ
      (bundleRankwiseEnvelopeError α β
        (bundleRankwiseDensityFloor α) τ) := by
  let μ := bundleRankwiseDensityFloor α
  have hμ : ∀ d, 0 < μ d := bundleRankwiseDensityFloor_pos hα
  refine
    { density_pos := hα
      density_le_one := hα_one
      defect_nonneg := hβ
      uniform_nonneg := hτ
      floor_pos := hμ
      rankFloor := ?_
      error_nonneg := bundleRankwiseEnvelopeError_nonneg
        (fun d => (hα d).le) (fun d => (hμ d).le) hτ
      error_mono_order := ?_
      error_mono_card := ?_
      step := ?_ }
  · intro i d hid
    exact bundleRankwiseDensityFloor_le α hid
  · intro d d' n hdd'
    exact (bundleRankwiseEnvelopeError_monotone_order α β μ τ n) hdd'
  · intro d n n' hnn'
    exact (bundleRankwiseEnvelopeError_monotone_card
      (fun q => (hα q).le) (fun q => (hμ q).le) hτ d) hnn'
  · intro d n
    have hstep :
        bundleRankwiseNextRow α β μ τ d
              (bundleRankwiseEnvelopeError α β μ τ d) n +
            bundleRankwiseStepIncrement α β μ τ
              (bundleRankwiseEnvelopeError α β μ τ d) d n ≤
          max (bundleRankwiseEnvelopeError α β μ τ d (n + 1))
            (bundleRankwiseNextRow α β μ τ d
                (bundleRankwiseEnvelopeError α β μ τ d) n +
              bundleRankwiseStepIncrement α β μ τ
                (bundleRankwiseEnvelopeError α β μ τ d) d n) :=
      le_max_right _ _
    simp [μ, bundleRankwiseStepIncrement, add_assoc] at hstep ⊢
