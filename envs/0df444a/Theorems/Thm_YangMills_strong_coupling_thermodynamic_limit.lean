-- Prove2me | Theorems.Thm_YangMills_strong_coupling_thermodynamic_limit
-- name    : YangMills.strong_coupling_thermodynamic_limit
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T13:01:26.364231+00:00
-- url     : https://prove2.me/theorems/19f55fb1-0a0e-4528-ad6f-e5fcdef57c71
-- title:
--   Thermodynamic limit of the plaquette expectation at strong coupling
-- statement:
--   **Existence of the thermodynamic limit at strong coupling.**
--
--   For $SU(N)$ Wilson lattice gauge theory there is a threshold $\beta_0>0$ such that for every
--   $0\le\beta<\beta_0$ the expectation of the plaquette energy density at the origin converges as
--   the torus grows:
--
--   $$\lim_{L\to\infty}\ \langle P_0\rangle_{L,\beta}\ \text{ exists in }\mathbb R .$$
--
--   Infinite-volume limits of local observables are the first thing a constructive programme needs:
--   the continuum theory is built from correlation functions of the infinite-volume state, and the
--   strong-coupling regime is where their existence can be established by a convergent expansion.
--   The statement is restricted to small $\beta$ deliberately — at large $\beta$ the existence of the
--   limit for all couplings is not known.
-- source:
--   E. Seiler, Gauge Theories as a Problem of Constructive Quantum Field Theory and Statistical Mechanics, Lecture Notes in Physics 159 (1982), Chapter 2 (convergent strong-coupling/polymer expansion and the infinite-volume limit); K. Osterwalder and E. Seiler, Ann. Physics 110 (1978) 440-471, Section 5.

import Definitions.Def_YangMills_Wilson_lattice

open MeasureTheory Filter Topology Finset

namespace YangMills

theorem strong_coupling_thermodynamic_limit
    (N : ℕ) (hN : 2 ≤ N) [MeasurableSpace (SU N)] [BorelSpace (SU N)]
    (μG : Measure (SU N)) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
    [μG.IsMulRightInvariant] :
    ∃ β₀ > 0, ∀ β : ℝ, 0 ≤ β → β < β₀ →
      ∃ P : ℝ, Tendsto (fun L : ℕ => wilsonExp L μG β fun U => plaqDensity U (0 : Site L))
        atTop (𝓝 P) := by sorry

end YangMills
