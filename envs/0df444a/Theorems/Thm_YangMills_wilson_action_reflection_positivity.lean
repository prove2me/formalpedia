-- Prove2me | Theorems.Thm_YangMills_wilson_action_reflection_positivity
-- name    : YangMills.wilson_action_reflection_positivity
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-13T12:54:11.265708+00:00
-- url     : https://prove2.me/theorems/ecb33ffe-df59-4e79-a9b8-db90d1d6f4dc
-- title:
--   Reflection positivity of the Wilson action
-- statement:
--   **Reflection positivity of the Wilson action** (Osterwalder–Seiler).
--
--   Work on the periodic lattice torus of even side $L+1$, with gauge group $SU(N)$, Haar
--   probability measure $\mu_G$, inverse coupling $\beta\ge0$, and let $\theta$ denote the
--   Osterwalder–Seiler link reflection in the hyperplane half way between the time slices $0$ and
--   $1$: on sites $(x^0,\vec x)\mapsto(1-x^0,\vec x)$, on spatial links the mirror image of the link,
--   and on temporal links the inverse of the mirror image.
--
--   Let $F_0,\dots,F_{m-1}$ be real observables each depending only on the gauge field on links whose
--   two endpoints lie in the time slices $1,\dots,(L+1)/2$, and let $c_0,\dots,c_{m-1}$ be real
--   numbers. Then
--
--   $$\sum_{j,l} c_j c_l\,\bigl\langle (F_j\circ\theta)\,F_l\bigr\rangle_{L,\beta}\ \ge\ 0,$$
--
--   i.e. the matrix $\bigl(\langle (F_j\circ\theta)F_l\rangle\bigr)_{j,l}$ is positive semi-definite.
--
--   Reflection positivity is the structural property that makes the Euclidean lattice theory a
--   quantum theory: it yields the physical Hilbert space and a self-adjoint transfer matrix, and it
--   is the hypothesis under which Osterwalder–Schrader reconstruction produces a positive
--   Hamiltonian. It is also the input to the standard proofs of the Källén–Lehmann representation and
--   of correlation inequalities on the lattice.
-- source:
--   K. Osterwalder and E. Seiler, Gauge field theories on a lattice, Ann. Physics 110 (1978) 440-471, Theorem 2.1 (link reflection positivity of the Wilson plaquette action); E. Seiler, Lecture Notes in Physics 159 (1982), Chapter 2, Theorem 2.1.

import Definitions.Def_YangMills_Wilson_lattice

open MeasureTheory Filter Topology Finset

namespace YangMills

theorem wilson_action_reflection_positivity
    (N : ℕ) (hN : 2 ≤ N) [MeasurableSpace (SU N)] [BorelSpace (SU N)]
    (μG : Measure (SU N)) [IsProbabilityMeasure μG] [μG.IsMulLeftInvariant]
    [μG.IsMulRightInvariant] [μG.IsInvInvariant]
    (L : ℕ) (hL : 2 ∣ (L + 1)) (β : ℝ) (hβ : 0 ≤ β)
    (m : ℕ) (F : Fin m → (Cfg N L → ℝ)) (hF : ∀ j, PosObs (F j)) (c : Fin m → ℝ) :
    0 ≤ ∑ j : Fin m, ∑ l : Fin m,
      c j * c l * wilsonExp L μG β (fun U => F j (cfgRefl U) * F l U) := by sorry

end YangMills
