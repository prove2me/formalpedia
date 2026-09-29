-- Prove2me | Theorems.Thm_YangMillsMassGap_wilson_reflection_positivity
-- name    : YangMillsMassGap.wilson_reflection_positivity
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-25T16:51:36.30117+00:00
-- url     : https://prove2.me/theorems/deb09107-7281-4a94-b7e1-6a2e1e467336
-- title:
--   Reflection positivity of Wilson's lattice gauge theory
-- statement:
--   Let $G$ be a compact group with a continuous unitary representation $\rho$, and let $\beta\ge0$. Let $F$ be a bounded measurable observable that depends only on the link variables in the positive-time half of the periodic lattice $(\mathbb Z/(2L+2))^4$. Then the Wilson expectation of $\overline{F(\theta U)}\,F(U)$ is a non-negative real number. Here $\theta$ is the reflection in the time-zero plane lying between lattice sites.
-- source:
--   A. Jaffe, E. Witten, *Quantum Yang–Mills Theory* (Clay Mathematics Institute Millennium Problem description), https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf, §6.5 ('Reflection positivity holds for the Wilson approximation [36]'); K. Osterwalder, E. Seiler, Ann. Phys. 110 (1978) 440–471

module

public import Mathlib
public import Definitions.Def_YMMG_Lattice

public section

namespace YangMillsMassGap
open scoped ComplexOrder
/-- **Reflection positivity of Wilson's lattice gauge theory** (Jaffe–Witten §6.5, citing
Osterwalder–Seiler): for `β ≥ 0` and every bounded measurable observable `F` depending only on
the links of the positive-time half lattice, `⟨(ΘF) F⟩_{β,L} ≥ 0`, where
`(ΘF)(U) = conj F(θU)`. -/
theorem wilson_reflection_positivity
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [MeasurableSpace G] [BorelSpace G]
    {N : ℕ} (ρ : G →* Matrix.unitaryGroup (Fin N) ℂ) (hρ : Continuous ρ)
    (L : ℕ) (β : ℝ) (hβ : 0 ≤ β) (F : GaugeConfig G L → ℂ) (hFm : Measurable F)
    (hFb : ∃ C : ℝ, ∀ U, ‖F U‖ ≤ C) (hFpos : DependsOnlyOnPositiveLinks F) :
    0 ≤ wilsonExpectation ρ L β (fun U => (starRingEnd ℂ) (F (reflectConfig U)) * F U) := by sorry
end YangMillsMassGap
