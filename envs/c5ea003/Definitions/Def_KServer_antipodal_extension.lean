-- Prove2me | Definitions.Def_KServer_antipodal_extension
-- name    : KServer_antipodal_extension
-- status  : Definition
-- author  : @Shuze Chen
-- created : 2026-09-01T05:23:38.56975+00:00
-- url     : https://prove2.me/theorems/a50f3978-2d05-4400-aeb9-37bf14e972fa
-- title:
--   The antipodal extension of a metric space
-- statement:
--   The **antipodal extension** of a metric space, following Koutsoupias (1999) and Coester--Koutsoupias (2021). A point $\bar p$ is an *antipode* of $p$ when $px + x\bar p = p\bar p$ for every $x$ --- every point lies on a geodesic between $p$ and $\bar p$. Most spaces have no antipodes, but every metric space embeds isometrically into one where every point has one: add a second copy $\bar M = \{\bar p : p \in M\}$ and set
--
--   $$d(\bar p, \bar q) = d(p,q), \qquad d(p, \bar q) = 2\Delta - d(p,q),$$
--
--   where $\Delta$ is (an upper bound on) the diameter of $M$. The result is a metric space of diameter $2\Delta$ in which $p$ and $\bar p$ are mutual antipodes at distance $2\Delta$.
--
--   This file realises the construction on the sum type $M \oplus M$: `antiD` is the distance (with simp lemmas for the four constructor cases), `antipodalExtension` packages it as a `MetricSpace` given $0 < \Delta$ and the diameter bound, the left injection is an isometric embedding (definitionally: the `inl`/`inl` case of `antiD` *is* `dist`), and the antipode map is `Sum.swap`, with `antiD_swap_left`/`antiD_swap_right` recording the complement identity $d(\bar p, q) = 2\Delta - d(p,q) = d(p,\bar q)$ and `antiD_le` the diameter bound $2\Delta$.
--
--   ## Role
--
--   The extension is the stage on which the Coester--Koutsoupias potential lives. For $k$ servers the potential is $\Phi_{x_1\dots x_k}(w) = \sum_{i=0}^k w(\bar x_i^{\,i}\, x_{i+1} \dots x_k)$, a sum of work-function values at configurations that mix original points with antipodes; the work function is that of the original instance, extended to the larger space, and the antipode identities are what drive its update property. The existence of the extension --- the metric axioms for `antiD` --- was published earlier as a bare distance function; this definition upgrades it to a bona fide `MetricSpace` so that the work function, quasiconvexity, duality and resolution machinery, all stated for an arbitrary metric space, apply on the extension verbatim.
-- source:
--   E. Koutsoupias, 'Weak adversaries for the k-server problem', FOCS 1999 (the extension construction); C. Coester, E. Koutsoupias, 'Towards the k-server conjecture: a unifying potential, pushing the frontier to the circle', ICALP 2021, arXiv:2102.10474, Section 'The k-server potential': antipodes, and the extension M ∪ M̄ with p̄q̄ = pq and p̄q = 2Δ − pq.

import Mathlib

set_option linter.unreachableTactic false
set_option linter.unusedTactic false

namespace KServer

/-- The distance function of the **antipodal extension** of a metric space `M`
with respect to the diameter bound `Δ`: on `M ⊕ M`, the left summand carries the
original metric, the right summand is a second copy `M̄` of `M` with `d(x̄,ȳ) = d(x,y)`,
and across the two copies `d(x,ȳ) = 2Δ - d(x,y)`. -/
noncomputable def antiD {M : Type} [MetricSpace M] (Δ : ℝ) :
    (M ⊕ M) → (M ⊕ M) → ℝ
  | Sum.inl x, Sum.inl y => dist x y
  | Sum.inr x, Sum.inr y => dist x y
  | Sum.inl x, Sum.inr y => 2 * Δ - dist x y
  | Sum.inr x, Sum.inl y => 2 * Δ - dist x y

@[simp] theorem antiD_inl_inl {M : Type} [MetricSpace M] (Δ : ℝ) (x y : M) :
    antiD Δ (Sum.inl x) (Sum.inl y) = dist x y := rfl

@[simp] theorem antiD_inr_inr {M : Type} [MetricSpace M] (Δ : ℝ) (x y : M) :
    antiD Δ (Sum.inr x) (Sum.inr y) = dist x y := rfl

@[simp] theorem antiD_inl_inr {M : Type} [MetricSpace M] (Δ : ℝ) (x y : M) :
    antiD Δ (Sum.inl x) (Sum.inr y) = 2 * Δ - dist x y := rfl

@[simp] theorem antiD_inr_inl {M : Type} [MetricSpace M] (Δ : ℝ) (x y : M) :
    antiD Δ (Sum.inr x) (Sum.inl y) = 2 * Δ - dist x y := rfl

/-- Reflecting one argument through the antipode map `Sum.swap` complements the
distance to `2Δ`. -/
theorem antiD_swap_left {M : Type} [MetricSpace M] (Δ : ℝ) (p q : M ⊕ M) :
    antiD Δ (Sum.swap p) q = 2 * Δ - antiD Δ p q := by
  rcases p with x | x <;> rcases q with y | y <;> simp [antiD, Sum.swap] <;> ring

theorem antiD_swap_right {M : Type} [MetricSpace M] (Δ : ℝ) (p q : M ⊕ M) :
    antiD Δ p (Sum.swap q) = 2 * Δ - antiD Δ p q := by
  rcases p with x | x <;> rcases q with y | y <;> simp [antiD, Sum.swap] <;> ring

/-- The **antipodal extension** of a metric space, as a metric space: `M ⊕ M`
carrying `antiD Δ`, where `Δ` is positive and bounds all distances of `M`.
`Sum.inl` is an isometric embedding of `M`, and `Sum.swap` sends every point to
its antipode at distance `2Δ`. -/
@[reducible] noncomputable def antipodalExtension (M : Type) [MetricSpace M] (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ) : MetricSpace (M ⊕ M) where
  dist := antiD Δ
  dist_self := by rintro (x | x) <;> simp [antiD]
  dist_comm := by rintro (x | x) (y | y) <;> simp [antiD, dist_comm]
  dist_triangle := by
    rintro (x | x) (y | y) (z | z) <;>
      simp only [antiD] <;>
      [ exact dist_triangle x y z;
        linarith [dist_triangle y x z, dist_comm y x];
        linarith [hΔ x y, hΔ y z, hΔ x z];
        linarith [dist_triangle x z y, dist_comm z y];
        linarith [dist_triangle x z y, dist_comm z y];
        linarith [hΔ x y, hΔ y z, hΔ x z];
        linarith [dist_triangle y x z, dist_comm y x];
        exact dist_triangle x y z ]
  eq_of_dist_eq_zero := by
    rintro (x | x) (y | y) h <;> simp only [antiD] at h
    · rw [dist_eq_zero] at h; rw [h]
    · exfalso; have := hΔ x y; linarith
    · exfalso; have := hΔ x y; linarith
    · rw [dist_eq_zero] at h; rw [h]

theorem antipodalExtension_dist (M : Type) [MetricSpace M] (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ) (p q : M ⊕ M) :
    @dist _ (antipodalExtension M Δ hΔ0 hΔ).toPseudoMetricSpace.toDist p q
      = antiD Δ p q := rfl

/-- Every distance of the antipodal extension is at most `2Δ`. -/
theorem antiD_le (M : Type) [MetricSpace M] (Δ : ℝ) (hΔ0 : 0 < Δ)
    (hΔ : ∀ x y : M, dist x y ≤ Δ) (p q : M ⊕ M) : antiD Δ p q ≤ 2 * Δ := by
  rcases p with x | x <;> rcases q with y | y <;> simp only [antiD] <;>
    [ linarith [hΔ x y]; linarith [dist_nonneg (x := x) (y := y)];
      linarith [dist_nonneg (x := x) (y := y)]; linarith [hΔ x y] ]

end KServer


