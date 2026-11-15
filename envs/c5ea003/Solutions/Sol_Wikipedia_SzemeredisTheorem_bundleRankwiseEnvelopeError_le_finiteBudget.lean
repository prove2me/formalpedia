-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.bundleRankwiseEnvelopeError_le_finiteBudget
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:27:05.559091+00:00
-- url     : https://prove2.me/submissions/16977304-6357-4b99-acda-c1fdae5dd00f

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
import Theorems.Thm_Wikipedia_SzemeredisTheorem_bundleRankwiseStepIncrement_le_of_lower_le

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
/-! ## Vanishing and continuous rankwise parameter paths -/
/-! ## Density-scaled finite-horizon selection -/
/-! ## Explicit finite-horizon sufficient bounds -/

open Wikipedia.SzemeredisTheorem in
/-- A finite-rank/cardinality estimate from separated numerical hypotheses.

`horizon` must reverse-double, because one counting step at rank `d + 1`
consults lower-order bundles of sizes `n + 1` and `2(n + 1)`.  The defect
hypothesis at rank `d + 1` mentions only `β (d + 1)` and `α (d + 1)`;
the uniformity hypothesis mentions only `τ` and `μ (d + 1)`.  Thus the two
analytic parameters can be scheduled independently once a common per-step
budget `η` and a harmless lower-error cap `B` have been fixed. -/
theorem solution
    {α β μ : ℕ → ℝ} {τ η B : ℝ}
    (hα : ∀ d, 0 ≤ α d) (hβ : ∀ d, 0 ≤ β d)
    (hμ : ∀ d, 0 ≤ μ d) (hτ : 0 ≤ τ) (hη : 0 ≤ η)
    (rankBound : ℕ) (horizon : ℕ → ℕ)
    (hreverse : ∀ d, d < rankBound →
      2 * horizon (d + 1) ≤ horizon d)
    (hzero : ∀ d, d ≤ rankBound → horizon d ≤ horizon 0)
    (hcap :
      (rankBound : ℝ) * (horizon 0 : ℝ) * η ≤ B)
    (hdefect : ∀ d, d < rankBound → ∀ n, n < horizon (d + 1) →
      Real.sqrt
            (β (d + 1) * (1 + B) * (1 + B)) /
          (α (d + 1)) ^ (n + 1) ≤ η / 2)
    (huniform : ∀ d, d < rankBound → ∀ n, n < horizon (d + 1) →
      τ / (μ (d + 1)) ^ (n + 1) ≤ η / 2) :
    ∀ d, d ≤ rankBound → ∀ n, n ≤ horizon d →
      bundleRankwiseEnvelopeError α β μ τ d n ≤
        (d : ℝ) * (horizon 0 : ℝ) * η := by
  intro d hd
  induction d with
  | zero =>
      intro n hn
      simp
  | succ d ih =>
      have hdlt : d < rankBound := Nat.lt_of_succ_le hd
      let lower := bundleRankwiseEnvelopeError α β μ τ d
      have hlower_nonneg : ∀ m, 0 ≤ lower m :=
        bundleRankwiseEnvelopeError_nonneg hα hμ hτ d
      have hdle : d ≤ rankBound := Nat.le_of_lt hdlt
      have hdbound :
          (d : ℝ) * (horizon 0 : ℝ) * η ≤ B := by
        have hdcast : (d : ℝ) ≤ rankBound := by exact_mod_cast hdle
        have hq0 : 0 ≤ (horizon 0 : ℝ) := by positivity
        have hscale : 0 ≤ (horizon 0 : ℝ) * η := mul_nonneg hq0 hη
        calc
          (d : ℝ) * (horizon 0 : ℝ) * η =
              (d : ℝ) * ((horizon 0 : ℝ) * η) := by ring
          _ ≤ (rankBound : ℝ) * ((horizon 0 : ℝ) * η) :=
            mul_le_mul_of_nonneg_right hdcast hscale
          _ = (rankBound : ℝ) * (horizon 0 : ℝ) * η := by ring
          _ ≤ B := hcap
      have hrow : ∀ m, m ≤ horizon (d + 1) →
          bundleRankwiseNextRow α β μ τ d lower m ≤
            (d : ℝ) * (horizon 0 : ℝ) * η + (m : ℝ) * η := by
        intro m hm
        induction m with
        | zero =>
            simp only [bundleRankwiseNextRow_zero, Nat.cast_zero, zero_mul,
              add_zero]
            exact mul_nonneg (mul_nonneg (by positivity) (by positivity)) hη
        | succ m ihm =>
            have hmle : m ≤ horizon (d + 1) := Nat.le_trans (Nat.le_succ m) hm
            have hm_lt : m < horizon (d + 1) := Nat.lt_of_succ_le hm
            have hsmall₁ : m + 1 ≤ horizon d := by
              have hrev := hreverse d hdlt
              omega
            have hsmall₂ : 2 * (m + 1) ≤ horizon d := by
              have hrev := hreverse d hdlt
              omega
            have hlower₁raw := ih hdle (m + 1) hsmall₁
            have hlower₂raw := ih hdle (2 * (m + 1)) hsmall₂
            have hlower₁ : lower (m + 1) ≤ B := hlower₁raw.trans hdbound
            have hlower₂ : lower (2 * (m + 1)) ≤ B := hlower₂raw.trans hdbound
            have hincrement :
                bundleRankwiseStepIncrement α β μ τ lower d m ≤ η :=
              bundleRankwiseStepIncrement_le_of_lower_le hα hβ lower d m
                hlower_nonneg hlower₁ hlower₂
                (hdefect d hdlt m hm_lt) (huniform d hdlt m hm_lt)
            rw [bundleRankwiseNextRow_succ]
            apply max_le
            · calc
                lower (m + 1) ≤
                    (d : ℝ) * (horizon 0 : ℝ) * η := hlower₁raw
                _ ≤ (d : ℝ) * (horizon 0 : ℝ) * η +
                    ((m + 1 : ℕ) : ℝ) * η :=
                  le_add_of_nonneg_right (mul_nonneg (by positivity) hη)
            · calc
                bundleRankwiseNextRow α β μ τ d lower m +
                      bundleRankwiseStepIncrement α β μ τ lower d m ≤
                    ((d : ℝ) * (horizon 0 : ℝ) * η + (m : ℝ) * η) + η :=
                  add_le_add (ihm hmle) hincrement
                _ = (d : ℝ) * (horizon 0 : ℝ) * η +
                    ((m + 1 : ℕ) : ℝ) * η := by
                  push_cast
                  ring
      intro n hn
      rw [bundleRankwiseEnvelopeError_succ_order]
      have hmain := hrow n hn
      have hnzero : n ≤ horizon 0 := hn.trans (hzero (d + 1) hd)
      have hncast : (n : ℝ) ≤ horizon 0 := by exact_mod_cast hnzero
      have hηscale : (n : ℝ) * η ≤ (horizon 0 : ℝ) * η :=
        mul_le_mul_of_nonneg_right hncast hη
      calc
        bundleRankwiseNextRow α β μ τ d lower n ≤
            (d : ℝ) * (horizon 0 : ℝ) * η + (n : ℝ) * η := hmain
        _ ≤ (d : ℝ) * (horizon 0 : ℝ) * η +
            (horizon 0 : ℝ) * η := add_le_add_right hηscale _
        _ = ((d + 1 : ℕ) : ℝ) * (horizon 0 : ℝ) * η := by
          push_cast
          ring
