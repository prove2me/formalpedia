-- Prove2me | Theorems.Thm_YangMills_yang_mills_existence_and_mass_gap
-- name    : YangMills.yang_mills_existence_and_mass_gap
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T13:38:33.250338+00:00
-- url     : https://prove2.me/theorems/ebe7680d-cc6a-4a7a-9403-5a423e6bd89e
-- title:
--   Yang–Mills existence and mass gap for $SU(N)$
-- statement:
--   This is the Clay Millennium problem *Quantum Yang–Mills theory* in the Euclidean formulation,
--   for the gauge groups $SU(N)$ with $N\ge2$.
--
--   Let $N\ge2$ and let $\mu_G$ be the Haar probability measure on $SU(N)$, i.e. a Borel probability
--   measure invariant under left and right translations. The assertion is that there exist a family
--   of Schwinger functions $(S_n)_{n\ge0}$ on $\mathbb R^4$ satisfying the Osterwalder–Schrader
--   axioms and a real number $\Delta>0$ such that:
--
--   1. **Non-triviality.** Some truncated two-point function is non-zero:
--      $S_2(f,g)-S_1(f)S_1(g)\neq 0$ for some test functions $f,g$.
--   2. **Mass gap.** For all test functions $f,g$ there is $C\ge0$ with
--      $$\bigl|S_2(f,g_t)-S_1(f)S_1(g_t)\bigr|\le C\,e^{-\Delta t},\qquad t\ge0,$$
--      where $g_t(x)=g(x-te_0)$ translates $g$ by $t$ units of Euclidean time.
--   3. **It is Yang–Mills.** $(S_n)$ is a continuum limit of $SU(N)$ Wilson lattice gauge theory:
--      there are lattice spacings $a_k\to0$, torus sides $L_k+1$ with $a_k(L_k+1)\to\infty$, inverse
--      couplings $\beta_k\to\infty$ and field normalisations $Z_k$ such that the lattice Schwinger
--      functions of the smeared, centred plaquette-density field converge to $S_n$.
--
--   Clause 3 is what pins the theory down as Yang–Mills rather than an arbitrary axiomatic field
--   theory, and clause 1 excludes the degenerate limits (for instance $Z_k=0$) in which all
--   connected correlations vanish. Clause 2 is the Euclidean form of the statement that the
--   Hamiltonian reconstructed from $(S_n)$ has spectrum contained in $\{0\}\cup[\Delta,\infty)$.
--
--   This statement is open. The Clay problem asks it for an arbitrary compact simple gauge group; the
--   present formalization covers the family $SU(N)$, $N\ge2$, which includes the physically relevant
--   $SU(3)$.
--
--   **Formalization Note.** Jaffe and Witten state the gap spectrally: the Hamiltonian $H$ of the
--   reconstructed theory has no spectrum in $(0,\Delta)$. Since the Hamiltonian only exists after
--   Osterwalder–Schrader reconstruction, which is not formalized here, the goal asserts the
--   Euclidean surrogate — exponential decay of the truncated two-point function at rate $\Delta$ —
--   and the existence part is expressed by exhibiting Schwinger functions satisfying OS0–OS3 that
--   arise as a Wilson scaling limit.
-- source:
--   A. Jaffe and E. Witten, Quantum Yang-Mills Theory, Clay Mathematics Institute Millennium Prize Problem description (2000), Problem statement on p. 6: 'Prove that for any compact simple gauge group G, a non-trivial quantum Yang-Mills theory exists on R^4 and has a mass gap Delta > 0.' https://www.claymath.org/wp-content/uploads/2022/06/yangmills.pdf

import Definitions.Def_YangMills_Wilson_lattice

open MeasureTheory Filter Topology Finset

namespace YangMills

theorem yang_mills_existence_and_mass_gap
    (N : ℕ) (hN : 2 ≤ N) [MeasurableSpace (SU N)] [BorelSpace (SU N)]
    (μG : Measure (SU N)) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
    [μG.IsMulRightInvariant] :
    ∃ (Q : OSTheory) (Δ : ℝ), 0 < Δ ∧ Q.IsNonTrivial ∧ Q.HasMassGap Δ ∧
      IsWilsonScalingLimit N μG Q := by sorry

end YangMills
