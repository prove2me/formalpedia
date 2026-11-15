-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cutCorrelation_eq_sum_boolean
-- name    : Wikipedia.SzemeredisTheorem.cutCorrelation_eq_sum_boolean
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:52:34.517203+00:00
-- url     : https://prove2.me/theorems/9e30fcdd-e359-48bb-bbc2-0d4c8232b6f9
-- title:
--   Exact Bernoulli expansion of a cut correlation
-- statement:
--   For a finite additive commutative group, real functions $f,g$, and any real deleted-coordinate test family $u$, the cut correlation equals the sum over all Boolean cut assignments of the Boolean cut correlation weighted by
--
--   $$
--   \prod_c\begin{cases}u_c,&b_c=1,\\1-u_c,&b_c=0.\end{cases}
--   $$
--
--   The index $c$ ranges over the scalar cut-test coordinates. This is an algebraic identity for arbitrary real tests; the weights need not be nonnegative.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/BooleanCutReduction.lean#L189-L244

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_BooleanCutReduction
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_DenseModel
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_PolynomialApproximation
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Mathlib.Topology.ContinuousMap.Weierstrass

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Reduction of bounded cut tests to Boolean cut tests

On a finite space, a `[0,1]`-valued cut-test family is a convex mixture of
its Boolean vertices.  Since every monomial in a cut correlation uses each
test coordinate at most once, the correlation is exactly the same convex
mixture of Boolean correlations.  Consequently it is enough to control the
finite family of Boolean cut tests in the dense-model theorem.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators Polynomial
/-! ## Finite Bernoulli mixtures -/
/-! ## Boolean cut coordinates -/

theorem Wikipedia.SzemeredisTheorem.cutCorrelation_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f g u =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutCorrelation r f g
            (cutTestFamilyOfBooleanAssignment b) := by sorry
