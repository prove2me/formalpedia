-- Prove2me | Theorems.Thm_YangMills_strong_coupling_exponential_clustering
-- name    : YangMills.strong_coupling_exponential_clustering
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T13:10:49.493329+00:00
-- url     : https://prove2.me/theorems/95a17fbb-6dc1-48fe-a56e-eec48326557d
-- title:
--   Exponential clustering at strong coupling (lattice mass gap)
-- statement:
--   **Exponential clustering of the lattice theory at strong coupling** (convergent strong-coupling
--   expansion; Osterwalder–Seiler, Seiler's lecture notes).
--
--   For $SU(N)$ Wilson lattice gauge theory there is an inverse coupling threshold $\beta_0>0$ and
--   constants $m>0$, $C\ge0$, all independent of the lattice size, such that for every
--   $0\le\beta<\beta_0$, every torus side $L+1$ and all sites $x,y$,
--
--   $$\bigl|\langle P_xP_y\rangle_{L,\beta}-\langle P_x\rangle_{L,\beta}\langle P_y\rangle_{L,\beta}\bigr|
--   \ \le\ C\,e^{-m\,d(x,y)},$$
--
--   where $P_x$ is the Wilson energy density at $x$ and $d$ is the $\ell^1$ graph distance on the
--   torus.
--
--   This is the lattice counterpart of the mass gap: the truncated correlation of two local
--   gauge-invariant observables decays exponentially in their separation, with a rate that does not
--   degrade as the volume grows. The uniformity in $L$ is what allows the estimate to survive the
--   thermodynamic limit.
-- source:
--   K. Osterwalder and E. Seiler, Gauge field theories on a lattice, Ann. Physics 110 (1978) 440-471, Section 5 (strong-coupling expansion: exponential decay of truncated correlations, uniformly in the volume); E. Seiler, Lecture Notes in Physics 159 (1982), Chapter 2.

import Definitions.Def_YangMills_Wilson_lattice

open MeasureTheory Filter Topology Finset

namespace YangMills

theorem strong_coupling_exponential_clustering
    (N : ℕ) (hN : 2 ≤ N) [MeasurableSpace (SU N)] [BorelSpace (SU N)]
    (μG : Measure (SU N)) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
    [μG.IsMulRightInvariant] :
    ∃ β₀ > 0, ∃ mgap > 0, ∃ C ≥ 0, ∀ β : ℝ, 0 ≤ β → β < β₀ →
      ∀ (L : ℕ) (x y : Site L),
        |wilsonExp L μG β (fun U => plaqDensity U x * plaqDensity U y) -
            wilsonExp L μG β (fun U => plaqDensity U x) *
              wilsonExp L μG β (fun U => plaqDensity U y)| ≤
          C * Real.exp (-mgap * (torusDist x y : ℝ)) := by sorry

end YangMills
