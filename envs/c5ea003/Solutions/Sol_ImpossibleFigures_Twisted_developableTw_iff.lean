-- Prove2me | solution 1 for ImpossibleFigures.Twisted.developableTw_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T06:19:11.447973+00:00
-- url     : https://prove2.me/submissions/c6cbe4ea-e5bc-4b2a-87fe-a65e8650d080

-- Sol generated from Geometry/TwistedDevelopability.lean
import Mathlib
import Definitions.Def_Geometry_TwistedDevelopability

/-!
# Impossible Figures VI: Orientation covers and signed holonomy

*Increment fields twisted by an orientation local system.*

The companion file `Geometry/CellularDevelopability.lean` classifies untwisted
increment fields on an arbitrary two–dimensional cell complex: developability is
equivalent to the vanishing of the period on the whole one–cycle group, hence to
vanishing curvature plus vanishing periods on a generating family of cycles.

This file treats the **twisted** case, which models non-orientable figures (Möbius
strips, Klein bottles) where the height coordinate is only defined up to a sign
that flips along orientation-reversing edges.  An **orientation local system** is
recorded by a weight function `w : E → ℤ` (in the geometric case `w e = ±1`); a
field `ω : E → A` is **twisted developable** when

`ω e = h (t e) - w e • h (s e)`

for some height field `h : V → A`.  The corresponding twisted boundary operator is
`∂ʷ e = [t e] - w e • [s e]`.

## Main results

* `period_eq_zero_of_developableTw` — twisted developability forces the period to
  vanish on every twisted one–cycle.
* `exists_half_period_of_developableTw` — the **anti-invariance condition**: on an
  orientation-reversing loop `ℓ` (a chain with `∂ʷ ℓ = 2 • [v₀]`, the algebraic
  shadow of a loop that lifts to a path between the two sheets of the orientation
  double cover) the period must be *divisible by two* in the coefficient group.
* `developableTw_iff` — **the twisted classification**: with a base point, chains
  joining it to every vertex (with odd sign holonomies) and an orientation-reversing
  loop `ℓ`, a twisted field is developable iff its periods vanish on all twisted
  cycles *and* its period on `ℓ` is twice some coefficient.
* `mobius_periods_insufficient` — a genuine **counterexample** showing the second
  condition is not implied by the first: on the one-vertex, one-edge complex with
  `w = -1` and coefficients `ℤ`, the twisted cycle group is trivial (so all period
  obstructions vanish) yet the unit field `ω ≡ 1` is not developable.  Signed
  holonomy is therefore a strictly new obstruction beyond ordinary cohomology.
-/

open ImpossibleFigures.Twisted

variable {V E A : Type*} [AddCommGroup A]

/-! ### Twisted chains and twisted developability -/




@[simp]
lemma boundaryTw_single (s t : E → V) (w : E → ℤ) (e : E) (k : ℤ) :
    boundaryTw s t w (Finsupp.single e k)
      = k • (Finsupp.single (t e) (1 : ℤ) - w e • Finsupp.single (s e) (1 : ℤ)) := by
  simp [boundaryTw]

@[simp]
lemma period_single (ω : E → A) (e : E) (k : ℤ) :
    period ω (Finsupp.single e k) = k • ω e := by
  simp [period]

/-! ### Necessary conditions -/

/-- The period of a twisted developable field is the height field evaluated on the
twisted boundary (twisted discrete Stokes). -/
theorem period_comp_boundaryTw {s t : E → V} {w : E → ℤ} {ω : E → A} {h : V → A}
    (hω : ∀ e, ω e = h (t e) - w e • h (s e)) :
    period ω = (Finsupp.linearCombination ℤ h).comp (boundaryTw s t w) := by
  apply Finsupp.lhom_ext
  intro e k
  simp only [period_single, LinearMap.comp_apply, boundaryTw_single, map_smul, map_sub,
    Finsupp.linearCombination_single, one_smul, hω e, smul_sub]

/-- **Twisted periods obstruct developability.** -/
theorem period_eq_zero_of_developableTw {s t : E → V} {w : E → ℤ} {ω : E → A}
    (hdev : DevelopableTw s t w ω) {z : E →₀ ℤ} (hz : boundaryTw s t w z = 0) :
    period ω z = 0 := by
  obtain ⟨h, hh⟩ := hdev
  rw [period_comp_boundaryTw hh]
  simp [hz]

/-- **The anti-invariance condition is necessary.**  On an orientation-reversing
loop `ℓ` — algebraically, a chain with `∂ʷ ℓ = 2 • [v₀]`, which is precisely a path
between the two sheets over `v₀` in the orientation double cover — the period of a
developable field is twice a coefficient. -/
theorem exists_half_period_of_developableTw {s t : E → V} {w : E → ℤ} {ω : E → A}
    {v₀ : V} {l : E →₀ ℤ} (hl : boundaryTw s t w l = (2 : ℤ) • Finsupp.single v₀ (1 : ℤ))
    (hdev : DevelopableTw s t w ω) :
    ∃ x : A, period ω l = x + x := by
  obtain ⟨h, hh⟩ := hdev
  refine ⟨h v₀, ?_⟩
  rw [period_comp_boundaryTw hh]
  simp [hl, two_smul, Finsupp.linearCombination_single]

/-! ### The twisted classification -/


/-! ### The Möbius counterexample: signed holonomy beyond periods -/














open ImpossibleFigures.Twisted in
theorem solution{s t : E → V} {w : E → ℤ} {v₀ : V}
    (hw : ∀ e, Odd (w e)) (c : V → (E →₀ ℤ)) (u : V → ℤ) (hu : ∀ v, Odd (u v))
    (hc : ∀ v, boundaryTw s t w (c v)
      = Finsupp.single v (1 : ℤ) - u v • Finsupp.single v₀ (1 : ℤ))
    (l : E →₀ ℤ) (hl : boundaryTw s t w l = (2 : ℤ) • Finsupp.single v₀ (1 : ℤ))
    (ω : E → A) :
    DevelopableTw s t w ω ↔
      (∀ z : E →₀ ℤ, boundaryTw s t w z = 0 → period ω z = 0)
        ∧ (∃ x : A, period ω l = x + x) := by
  constructor
  · intro hdev
    exact ⟨fun z hz => period_eq_zero_of_developableTw hdev hz,
      exists_half_period_of_developableTw hl hdev⟩
  · rintro ⟨hcyc, x, hx⟩
    refine ⟨fun v => period ω (c v) + u v • x, fun e => ?_⟩
    -- the sign discrepancy along the edge `e` is even
    obtain ⟨m, hm⟩ : ∃ m : ℤ, u (t e) - w e * u (s e) = m + m := by
      have h1 : Odd (u (t e)) := hu _
      have h2 : Odd (w e * u (s e)) := (hw e).mul (hu _)
      obtain ⟨m, hm⟩ := h1.sub_odd h2
      exact ⟨m, by omega⟩
    -- correct the edge chain by `m` copies of the orientation-reversing loop
    set z : E →₀ ℤ := Finsupp.single e 1 - c (t e) + w e • c (s e) - m • l with hz_def
    have hzcyc : boundaryTw s t w z = 0 := by
      have expand : boundaryTw s t w z
          = ((u (t e) - w e * u (s e)) - (m + m)) • Finsupp.single v₀ (1 : ℤ) := by
        simp only [hz_def, map_add, map_sub, map_smul, boundaryTw_single, hc, hl, one_smul]
        module
      rw [expand, hm, sub_self, zero_smul]
    have hzp := hcyc _ hzcyc
    simp only [hz_def, map_add, map_sub, map_smul, period_single, one_smul, hx] at hzp
    have hmx : m • (x + x) = (u (t e) - w e * u (s e)) • x := by
      rw [hm]; module
    rw [hmx] at hzp
    linear_combination (norm := module) hzp
