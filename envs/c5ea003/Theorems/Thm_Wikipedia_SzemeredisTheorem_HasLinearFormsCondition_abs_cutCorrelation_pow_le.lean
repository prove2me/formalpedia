-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HasLinearFormsCondition_abs_cutCorrelation_pow_le
-- name    : Wikipedia.SzemeredisTheorem.HasLinearFormsCondition.abs_cutCorrelation_pow_le
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:28:38.380353+00:00
-- url     : https://prove2.me/theorems/eafb76aa-aa56-4b5b-86c9-183e4579a60c
-- title:
--   A linear-forms condition bounds powered cut correlations
-- statement:
--   Let $N\ne0$ and $n\in\mathbb N$, let $\nu:\mathbb Z/N\mathbb Z\to\mathbb R$, and assume the $(n+2)$-linear-forms condition with error $\eta$. If $N$ is coprime to $(n+1)!$, every absolutely bounded arity-$(n+1)$ cut-test family $u$ satisfies $|\operatorname{cutCorrelation}_{n+1}(\nu,1,u)|^{2^{n+1}}\le2^{2^{n+1}}\eta$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/FaceMoments.lean#L309-L343

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_GeneralizedConvolution
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Centered moments on one progression face

The CFZ linear-forms condition controls every Boolean subproduct of the
forms belonging to a fixed deleted coordinate.  Inclusion--exclusion then
bounds the product of all centered factors on that face.  This is the
linear-forms estimate that appears at the endpoint of the generalized
von Neumann Cauchy--Schwarz argument.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.HasLinearFormsCondition.abs_cutCorrelation_pow_le
    {n N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η : ℝ}
    (h : HasLinearFormsCondition (n + 2) N ν η)
    (hN : Nat.Coprime N (Nat.factorial (n + 1)))
    (u : CutTestFamily (ZMod N) (n + 1))
    (hu : IsAbsBoundedCutTest u) :
    |cutCorrelation (n + 1) ν (fun _ => 1) u| ^
        (2 ^ (n + 1)) ≤
      (2 : ℝ) ^ (2 ^ (n + 1)) * η := by sorry
