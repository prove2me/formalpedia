-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_faceCenteredProduct_mul_linearFormsProduct_eq_sum
-- name    : Wikipedia.SzemeredisTheorem.mean_faceCenteredProduct_mul_linearFormsProduct_eq_sum
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:49.163521+00:00
-- url     : https://prove2.me/theorems/099d6c58-db80-47e1-a0d8-fa23ec85acdf
-- title:
--   Endpoint expansion with an additional linear-forms product
-- statement:
--   Let $N\ge1$ and $k\ge0$ be integers, let $\nu:\mathbb Z/N\mathbb Z\to\mathbb R$, and choose a face index $j\in\{0,\ldots,k-1\}$. Let $e$ be a selected linear-forms exponent which selects no form on face $j$. Multiplying the centered face product by the remaining selected product and averaging gives
--   $$
--   \mathbb E_x[C_{\nu,j}(x)L_{\nu,e}(x)]
--   =\sum_{b}\operatorname{sgn}(b)\,\mathbb E_x L_{\nu,e[j\leftarrow b]}(x).
--   $$
--   The sum is over Boolean selections on the deleted-coordinate cube of face $j$; its sign is the product of $-1$ for unselected entries and $1$ for selected entries. The overwritten exponent agrees with $e$ off face $j$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/WeightedStrongLinearForms.lean#L111-L148

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearForms
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
# Weighted endpoint of the strong linear-forms argument

The CFZ densification proof applies Cauchy--Schwarz repeatedly to a
centered factor on one simplex face.  At the final doubled stage, every
remaining relatively bounded factor has been replaced by either its
majorant or by one.  The resulting expression is

* the product of all centered copies of the selected face; times
* an arbitrary Boolean-selected subproduct of the other CFZ forms.

This file proves the exact quantitative linear-forms estimate for that
endpoint.  The still-missing recursive Cauchy--Schwarz bridge belongs in
the same module after this algebraic target.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.mean_faceCenteredProduct_mul_linearFormsProduct_eq_sum
    {k N : ℕ} [NeZero N]
    (ν : ZMod N → ℝ) (j : Fin k)
    (other : LinearFormsExponent k)
    (hother : ∀ ω, other j ω = false) :
    mean (fun x =>
        faceCenteredProduct k N ν j x *
          linearFormsProduct k N ν other x) =
      ∑ face : BooleanCube (DeletedCube k j),
        cubeSign face *
          mean (linearFormsProduct k N ν
            (overwriteFaceExponent j face other)) := by sorry
