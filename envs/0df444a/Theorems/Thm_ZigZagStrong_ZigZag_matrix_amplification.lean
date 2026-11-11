-- Prove2me | Theorems.Thm_ZigZagStrong_ZigZag_matrix_amplification
-- name    : ZigZagStrong.ZigZag.matrix_amplification
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:05:15.573208+00:00
-- url     : https://prove2.me/theorems/538514b0-e8f4-4b3e-80c3-c84d5afadcbc
-- title:
--   Proposition 2.5 — matrix amplification and full spectral convergence
-- statement:
--   Let $u_n$ be random unitary $r$-tuples in increasing finite dimensions and let $u$ be a fixed unitary tuple on a complex Hilbert space. Scalar-polynomial strong convergence holds if and only if every matrix-coefficient polynomial, without a self-adjointness restriction, satisfies
--   $$\|P(u_n)\|\longrightarrow\|P(u)\|\quad\text{in probability}.$$
--   Under strong convergence, for every positive matrix size and every polynomial whose evaluations are self-adjoint almost surely at every size and at the limit,
--   $$d_H(\operatorname{spec}P(u_n),\operatorname{spec}P(u))\longrightarrow0.$$
--   The random tuples carry arbitrary Borel probability laws. This supplies both directions of amplification and the entire spectral conclusion.
--
--   Differences from the source:
--   - encoding: Random unitary matrices; self-adjoint evaluations for every n → Borel probability laws directly on unitary tuples; almost-sure self-adjointness at each n; reason: Passing from a random variable to its law and discarding null sets changes no probability; dimensions start at one and spectral matrix sizes are positive.
-- source:
--   Gal Maor, Alon Dogon, STOC 2027 submission #371 (October 2026), Proposition 2.5, p. 9.

import Definitions.Def_ZigZagStrong_ZigZag_Covers

set_option autoImplicit false
noncomputable section

namespace ZigZagStrong.ZigZag
open Filter MeasureTheory
open scoped BigOperators Topology

theorem matrix_amplification {r : ℕ} {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F] [CompleteSpace F]
  (μ : ∀ n : ℕ, Measure (UnitaryTuple r (EuclideanSpace ℂ (Fin (n+1)))))
  [∀ n, IsProbabilityMeasure (μ n)] (u : UnitaryTuple r F) :
  (StrongConvergence (fun n A => (μ n).real A) (fun _ ω => ω.val) u.val ↔
    ∀ D : ℕ, ∀ P : StrongConv.NCPoly D r,
      ProbConverges (fun n A => (μ n).real A)
        (fun _ ω => ‖P.eval ω.val‖) ‖P.eval u.val‖) ∧
  (StrongConvergence (fun n A => (μ n).real A) (fun _ ω => ω.val) u.val →
    ∀ D : ℕ, 0 < D → ∀ P : StrongConv.NCPoly D r,
      (∀ n, ∀ᵐ ω ∂μ n, IsSelfAdjoint (P.eval ω.val)) → IsSelfAdjoint (P.eval u.val) →
      ProbConverges (fun n A => (μ n).real A)
        (fun _ ω => spectrumDistance (P.eval ω.val) (P.eval u.val)) 0) := by sorry

end ZigZagStrong.ZigZag
