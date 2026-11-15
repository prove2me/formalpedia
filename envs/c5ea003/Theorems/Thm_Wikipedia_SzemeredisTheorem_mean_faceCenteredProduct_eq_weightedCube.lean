-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_faceCenteredProduct_eq_weightedCube
-- name    : Wikipedia.SzemeredisTheorem.mean_faceCenteredProduct_eq_weightedCube
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:46.222209+00:00
-- url     : https://prove2.me/theorems/47c98588-7366-4b41-825f-1b1d9d5b1230
-- title:
--   A centered AP face average is a weighted cube average
-- statement:
--   Let $n\ge0$ and $N\ge1$ be integers, let $\nu:\mathbb Z/N\mathbb Z\to\mathbb R$, and choose $j\in\{0,\ldots,n\}$. Let $\sigma_j$ be the increasing map skipping $j$, and set $c_{j,t}=\sigma_j(t)-j$ modulo $N$. Then the centered AP face product satisfies
--   $$
--   \mathbb E_x C_{\nu,j}(x)=\mathbb E_y\prod_{\omega\in\{0,1\}^{n}}
--   \left(\nu\!\left(\sum_{t=0}^{n-1}c_{j,t}y_{t,\omega_t}\right)-1\right).
--   $$
--   Here $y$ assigns two residues to each of the $n$ remaining coordinates. This equality needs no factorial-coprimality assumption.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/FaceMoments.lean#L171-L206

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

theorem Wikipedia.SzemeredisTheorem.mean_faceCenteredProduct_eq_weightedCube
    (n N : ℕ) [NeZero N] (ν : ZMod N → ℝ)
    (j : Fin (n + 1)) :
    mean (faceCenteredProduct (n + 1) N ν j) =
      mean (fun y : Fin n → Bool → ZMod N =>
        ∏ ω : Fin n → Bool,
          (ν (∑ t : Fin n,
            ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
              ZMod N) * y t (ω t))) - 1)) := by sorry
