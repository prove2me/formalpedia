-- Prove2me | Theorems.Thm_YangMills_suN_wilson_strong_coupling_area_law
-- name    : YangMills.suN_wilson_strong_coupling_area_law
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T13:36:00.035888+00:00
-- url     : https://prove2.me/theorems/6aa9ff65-f9d9-4bc2-b161-727151f0d409
-- title:
--   Area law for Wilson loops at strong coupling
-- statement:
--   **Area law for Wilson loops at strong coupling** (Wilson 1974; Osterwalder–Seiler 1978).
--
--   For $SU(N)$ Wilson lattice gauge theory there are $\beta_0>0$, a string tension $\sigma>0$ and a
--   constant $C\ge0$, independent of the lattice size, such that for every $0\le\beta<\beta_0$ and
--   every rectangle $R\times T$ with $R,T\ge1$ fitting in the torus of side $L+1$ (i.e.
--   $2R\le L+1$ and $2T\le L+1$),
--
--   $$\bigl|\langle W(R,T)\rangle_{L,\beta}\bigr|\ \le\ C\,e^{-\sigma RT},$$
--
--   where $W(R,T)$ is the normalised real trace of the holonomy around the $R\times T$ rectangle
--   based at the origin in the $(1,0)$ plane.
--
--   Decay in the *area* $RT$, rather than in the perimeter, is Wilson's criterion for confinement:
--   the static quark–antiquark potential grows linearly with the separation, with slope $\sigma$.
--   At strong coupling this is a theorem; whether it persists in the continuum limit is part of what
--   the mass gap problem is about.
--
--   **Naming note.** The declaration is called `YangMills.suN_wilson_strong_coupling_area_law`: the
--   name `YangMills.strong_coupling_area_law` is already taken on the platform by a differently
--   formalized statement (an arbitrary compact gauge group with a unitary representation, in a
--   multi-scale box), so this mission's $SU(N)$ Wilson-lattice version carries a distinct identifier.
-- source:
--   K. G. Wilson, Confinement of quarks, Phys. Rev. D 10 (1974) 2445-2459, Section III (strong-coupling area law); K. Osterwalder and E. Seiler, Ann. Physics 110 (1978) 440-471, Section 6; E. Seiler, Lecture Notes in Physics 159 (1982), Chapter 2, Theorem 2.5.

import Definitions.Def_YangMills_Wilson_lattice

open MeasureTheory Filter Topology Finset

namespace YangMills

theorem suN_wilson_strong_coupling_area_law
    (N : ℕ) (hN : 2 ≤ N) [MeasurableSpace (SU N)] [BorelSpace (SU N)]
    (μG : Measure (SU N)) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
    [μG.IsMulRightInvariant] :
    ∃ β₀ > 0, ∃ σ > 0, ∃ C ≥ 0, ∀ β : ℝ, 0 ≤ β → β < β₀ →
      ∀ L R T : ℕ, 1 ≤ R → 1 ≤ T → 2 * R ≤ L + 1 → 2 * T ≤ L + 1 →
        |wilsonExp L μG β (wilsonLoop R T)| ≤ C * Real.exp (-σ * (R : ℝ) * (T : ℝ)) := by sorry

end YangMills
