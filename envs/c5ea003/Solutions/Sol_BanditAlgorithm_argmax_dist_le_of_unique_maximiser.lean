-- Prove2me | solution 1 for BanditAlgorithm.argmax_dist_le_of_unique_maximiser
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-08-01T04:19:18.059305+00:00
-- url     : https://prove2.me/submissions/7501017e-c7e6-4bfa-ac7d-d90863751493

import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# A maximiser depends continuously on the parameter where it is unique

`Solutions/TrackingCesaro.lean` derives the convergence of the tracked targets
`α*(μ̂(s)) → α*(μ)` from `ContinuousAt α* μ`, and flags that continuity is
genuinely needed: `α*` is only required to *select* an optimal allocation, and a
selection that jumps cannot be tracked.  This file supplies the continuity.

A selection of maximisers is not continuous in general — when the maximiser is
not unique the selection can jump between two of them arbitrarily.  Uniqueness at
the point of interest is exactly what rules this out, and it is all that is
needed: nothing is assumed about maximisers at nearby parameters, which may well
be non-unique.

## Statement

For `F : X → A → ℝ` jointly continuous along `univ ×ˢ S` and `S` compact, if
`a₀` is the *only*
maximiser of `F x₀` on `S`, then every maximiser of `F x` lies close to `a₀` once
`x` is close to `x₀`:

  `∀ ε > 0, ∃ δ > 0, ∀ x, dist x x₀ < δ → ∀ a ∈ argmax_S (F x), dist a a₀ < ε`.

This is the argmax ("upper hemicontinuity") half of Berge's maximum theorem,
specialised to a singleton argmax, where it becomes an honest continuity
statement rather than a set-valued one.

## Proof

Contradiction plus compactness.  If the conclusion fails there are `x_n → x₀`
and maximisers `a_n` of `F x_n` staying `ε` away from `a₀`.  Compactness of `S`
extracts `a_{φ(n)} → a`, still `ε` away from `a₀`, hence `a ≠ a₀`.  Passing to
the limit in `F x_{φ(n)} a_{φ(n)} ≥ F x_{φ(n)} b` — legitimate because `F` is
jointly continuous and `b` is held fixed — shows `a` maximises `F x₀`.
Uniqueness gives `a = a₀`, the contradiction.

Joint continuity is what makes the limit step work: separate continuity in each
argument would not let `F x_{φ(n)} a_{φ(n)}` be compared with `F x₀ a`.  It is
only needed along `univ ×ˢ S`, since every point the argument evaluates `F` at
is feasible.
-/

open Filter Topology Metric

namespace BanditAlgorithm

variable {X A : Type*} [MetricSpace X] [MetricSpace A]

/-- `a` maximises `F x` over `S`. -/
def IsMaxOnSet (F : X → A → ℝ) (S : Set A) (x : X) (a : A) : Prop :=
  a ∈ S ∧ ∀ b ∈ S, F x b ≤ F x a

/-! ## The main estimate -/

/-- **Maximisers near `x₀` are near the unique maximiser at `x₀`.**

Continuity of `F` is only required *along the feasible set* `univ ×ˢ S`.  This
matters for the intended application: the Track-and-Stop objective involves
`α_a α_b/(α_a + α_b)`, which is continuous on the closed simplex but genuinely
discontinuous off it, where the denominator can vanish with the numerator
nonzero. -/
theorem exists_delta_forall_isMaxOnSet_dist_lt {S : Set A} (hS : IsCompact S)
    {F : X → A → ℝ}
    (hF : ContinuousOn (fun p : X × A ↦ F p.1 p.2) (Set.univ ×ˢ S))
    {x₀ : X} {a₀ : A}
    (huniq : ∀ a, IsMaxOnSet F S x₀ a → a = a₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x : X, dist x x₀ < δ →
      ∀ a : A, IsMaxOnSet F S x a → dist a a₀ < ε := by
  by_contra hcon
  push_neg at hcon
  -- a counterexample at every scale `1/(n+1)`
  have hpick : ∀ n : ℕ, ∃ p : X × A,
      dist p.1 x₀ < 1 / ((n : ℝ) + 1) ∧ IsMaxOnSet F S p.1 p.2 ∧ ε ≤ dist p.2 a₀ := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨x, hx, a, hamax, hae⟩ := hcon (1 / ((n : ℝ) + 1)) hpos
    exact ⟨(x, a), hx, hamax, hae⟩
  choose q hq1 hq2 hq3 using hpick
  -- the parameters converge
  have hx : Tendsto (fun n ↦ (q n).1) atTop (𝓝 x₀) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (fun n ↦ dist_nonneg) (fun n ↦ (hq1 n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  -- the maximisers subconverge
  obtain ⟨a, haS, φ, hφ, hlim⟩ := hS.tendsto_subseq (fun n ↦ (hq2 n).1)
  have hφtop : Tendsto φ atTop atTop := hφ.tendsto_atTop
  -- the limit is still `ε` away from `a₀`
  have hfar : ε ≤ dist a a₀ := by
    have hd : Tendsto (fun n ↦ dist (q (φ n)).2 a₀) atTop (𝓝 (dist a a₀)) :=
      hlim.dist tendsto_const_nhds
    exact ge_of_tendsto hd (Eventually.of_forall fun n ↦ hq3 (φ n))
  -- the limit maximises `F x₀`
  have hxsub : Tendsto (fun n ↦ (q (φ n)).1) atTop (𝓝 x₀) := hx.comp hφtop
  -- limits of `F` along sequences that stay in the feasible set
  have key : ∀ c ∈ S, ∀ z : ℕ → A, (∀ n, z n ∈ S) → Tendsto z atTop (𝓝 c) →
      Tendsto (fun n ↦ F (q (φ n)).1 (z n)) atTop (𝓝 (F x₀ c)) := by
    intro c hc z hz hzlim
    have hcw : ContinuousWithinAt (fun p : X × A ↦ F p.1 p.2) (Set.univ ×ˢ S) (x₀, c) :=
      hF (x₀, c) ⟨Set.mem_univ _, hc⟩
    have hpair : Tendsto (fun n ↦ ((q (φ n)).1, z n)) atTop
        (𝓝[Set.univ ×ˢ S] (x₀, c)) := by
      rw [tendsto_nhdsWithin_iff]
      exact ⟨hxsub.prodMk_nhds hzlim,
        Eventually.of_forall fun n ↦ ⟨Set.mem_univ _, hz n⟩⟩
    exact Filter.Tendsto.comp hcw hpair
  have hmax : IsMaxOnSet F S x₀ a := by
    refine ⟨haS, fun b hb ↦ ?_⟩
    have hleft : Tendsto (fun n ↦ F (q (φ n)).1 b) atTop (𝓝 (F x₀ b)) :=
      key b hb (fun _ ↦ b) (fun _ ↦ hb) tendsto_const_nhds
    have hright : Tendsto (fun n ↦ F (q (φ n)).1 (q (φ n)).2) atTop (𝓝 (F x₀ a)) :=
      key a haS (fun n ↦ (q (φ n)).2) (fun n ↦ (hq2 (φ n)).1) hlim
    refine le_of_tendsto_of_tendsto hleft hright ?_
    exact Eventually.of_forall fun n ↦ (hq2 (φ n)).2 b hb
  -- uniqueness closes the contradiction
  have : a = a₀ := huniq a hmax
  rw [this, dist_self] at hfar
  exact absurd hfar (not_le.mpr hε)

/-! ## Continuity of a selection

A *selection* is a function `sel : X → A` picking, for each parameter, some
maximiser.  The estimate above says any such selection is continuous at a point
of uniqueness — however it breaks ties elsewhere. -/

/-- **A selection of maximisers is continuous at every point where the maximiser
is unique.** -/
theorem continuousAt_of_isMaxOnSet {S : Set A} (hS : IsCompact S)
    {F : X → A → ℝ}
    (hF : ContinuousOn (fun p : X × A ↦ F p.1 p.2) (Set.univ ×ˢ S))
    {x₀ : X} {sel : X → A}
    (hsel : ∀ x, IsMaxOnSet F S x (sel x))
    (huniq : ∀ a, IsMaxOnSet F S x₀ a → a = sel x₀) :
    ContinuousAt sel x₀ := by
  rw [ContinuousAt, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hmain⟩ :=
    exists_delta_forall_isMaxOnSet_dist_lt hS hF (a₀ := sel x₀) huniq hε
  rw [Metric.eventually_nhds_iff]
  exact ⟨δ, hδ, fun {x} hx ↦ hmain x hx (sel x) (hsel x)⟩

/-! ## Sequential form

The form the tracking argument consumes: parameters converging to `x₀` push any
choice of maximisers to the maximiser at `x₀`.  Note this does *not* require the
maximisers `a n` to be chosen by a single selection — an algorithm computing an
optimal allocation afresh at every round need not be consistent in its
tie-breaking. -/

/-- The eventual form: the maximiser property is only needed from some index on,
which is what a plug-in rule provides — early estimates need not even have a
maximiser of the right shape. -/
theorem tendsto_of_eventually_isMaxOnSet {S : Set A} (hS : IsCompact S)
    {F : X → A → ℝ}
    (hF : ContinuousOn (fun p : X × A ↦ F p.1 p.2) (Set.univ ×ˢ S))
    {x₀ : X} {a₀ : A} (huniq : ∀ a, IsMaxOnSet F S x₀ a → a = a₀)
    {x : ℕ → X} (hx : Tendsto x atTop (𝓝 x₀))
    {a : ℕ → A} (ha : ∀ᶠ n in atTop, IsMaxOnSet F S (x n) (a n)) :
    Tendsto a atTop (𝓝 a₀) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hmain⟩ := exists_delta_forall_isMaxOnSet_dist_lt hS hF huniq hε
  have hev : ∀ᶠ n in atTop, dist (x n) x₀ < δ := by
    rw [tendsto_iff_dist_tendsto_zero] at hx
    exact (hx.eventually (gt_mem_nhds hδ))
  filter_upwards [hev, ha] with n hn hna
  exact hmain (x n) hn (a n) hna

theorem tendsto_of_isMaxOnSet {S : Set A} (hS : IsCompact S)
    {F : X → A → ℝ}
    (hF : ContinuousOn (fun p : X × A ↦ F p.1 p.2) (Set.univ ×ˢ S))
    {x₀ : X} {a₀ : A} (huniq : ∀ a, IsMaxOnSet F S x₀ a → a = a₀)
    {x : ℕ → X} (hx : Tendsto x atTop (𝓝 x₀))
    {a : ℕ → A} (ha : ∀ n, IsMaxOnSet F S (x n) (a n)) :
    Tendsto a atTop (𝓝 a₀) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hmain⟩ := exists_delta_forall_isMaxOnSet_dist_lt hS hF huniq hε
  have hev : ∀ᶠ n in atTop, dist (x n) x₀ < δ := by
    rw [tendsto_iff_dist_tendsto_zero] at hx
    exact (hx.eventually (gt_mem_nhds hδ))
  filter_upwards [hev] with n hn
  exact hmain (x n) hn (a n) (ha n)

end BanditAlgorithm

theorem _root_.solution {X A : Type*} [MetricSpace X] [MetricSpace A]
    {S : Set A} (hS : IsCompact S) {F : X → A → ℝ}
    (hF : ContinuousOn (fun q : X × A ↦ F q.1 q.2) (Set.univ ×ˢ S))
    {x₀ : X} {a₀ : A}
    (huniq : ∀ a, a ∈ S → (∀ b ∈ S, F x₀ b ≤ F x₀ a) → a = a₀)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ x : X, dist x x₀ < δ →
      ∀ a : A, a ∈ S → (∀ b ∈ S, F x b ≤ F x a) → dist a a₀ < ε := by
  obtain ⟨δ, hδ, h⟩ :=
    BanditAlgorithm.exists_delta_forall_isMaxOnSet_dist_lt hS hF (a₀ := a₀)
      (fun a ha ↦ huniq a ha.1 ha.2) hε
  exact ⟨δ, hδ, fun x hx a haS hamax ↦ h x hx a ⟨haS, hamax⟩⟩
