-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_abs_cutCorrelation_le_of_boolean
-- name    : Wikipedia.SzemeredisTheorem.abs_cutCorrelation_le_of_boolean
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:40:36.127732+00:00
-- url     : https://prove2.me/theorems/59317dc3-0ab3-43f9-86af-6b00e0c86879
-- title:
--   Boolean cut-correlation bounds extend to bounded cut tests
-- statement:
--   Let $G$ be a finite additive commutative group, $f,g:G\to\mathbb R$, and $\varepsilon\in\mathbb R$. If every Boolean arity-$r$ cut assignment has absolute cut correlation between $f,g$ at most $\varepsilon$, then the same bound holds for every bounded arity-$r$ cut-test family.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/BooleanCutReduction.lean#L246-L286

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

theorem Wikipedia.SzemeredisTheorem.abs_cutCorrelation_le_of_boolean
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (u : CutTestFamily G r) (hu : IsBoundedCutTest u)
    (hboolean :
      ∀ b : BooleanCutAssignment G r,
        |cutCorrelation r f g
          (cutTestFamilyOfBooleanAssignment b)| ≤ ε) :
    |cutCorrelation r f g u| ≤ ε := by sorry
