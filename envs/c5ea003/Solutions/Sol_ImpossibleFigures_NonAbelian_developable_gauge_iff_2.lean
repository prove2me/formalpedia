-- Prove2me | solution 2 for ImpossibleFigures.NonAbelian.developable_gauge_iff
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T22:41:14.007987+00:00
-- url     : https://prove2.me/submissions/80360bb5-dec5-448d-be1f-11bde40d5ac0

import Mathlib
import Definitions.Def_Geometry_NonAbelianHolonomy
open ImpossibleFigures.NonAbelian in
theorem solution {V E G : Type*} [Group G] {s t : E → V} (H : V → G) (ω : E → G) (base : V)
    (hconn : ∀ v : V, ∃ l, IsWalk s t base v l) :
    Developable s t (ImpossibleFigures.NonAbelian.gauge s t H ω) ↔ Developable s t ω := by
  constructor
  · -- undo the gauge: `ω = (H⁻¹ K)(t) · ((H⁻¹ K)(s))⁻¹`
    rintro ⟨K, hK⟩
    refine ⟨fun v => (H v)⁻¹ * K v, fun e => ?_⟩
    have := hK e
    simp only [ImpossibleFigures.NonAbelian.gauge] at this
    calc ω e = (H (t e))⁻¹ * (H (t e) * ω e * (H (s e))⁻¹) * H (s e) := by group
      _ = (H (t e))⁻¹ * (K (t e) * (K (s e))⁻¹) * H (s e) := by rw [this]
      _ = (H (t e))⁻¹ * K (t e) * ((H (s e))⁻¹ * K (s e))⁻¹ := by group
  · -- compose the gauges: `gauge ω = (H K)(t) · ((H K)(s))⁻¹`
    rintro ⟨K, hK⟩
    refine ⟨fun v => H v * K v, fun e => ?_⟩
    simp only [ImpossibleFigures.NonAbelian.gauge]
    rw [hK e]
    group
