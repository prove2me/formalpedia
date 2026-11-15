-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_faceCenteredProduct_eq_boxMoment
-- name    : Wikipedia.SzemeredisTheorem.mean_faceCenteredProduct_eq_boxMoment
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:46.614989+00:00
-- url     : https://prove2.me/theorems/dc613fed-b1d1-428b-8d71-4620a3c501d0
-- title:
--   A centered AP face moment is a box moment
-- statement:
--   Let $n\ge0$ and $N\ge1$ be integers with $\gcd(N,n!)=1$. Let $\nu:\mathbb Z/N\mathbb Z\to\mathbb R$ and choose $j\in\{0,\ldots,n\}$. The normalized mean of the centered product on face $j$ of the $(n+1)$-face AP system is
--   $$
--   \mathbb E_x C_{\nu,j}(x)=B_n\!\left(y\longmapsto\nu\!\left(\sum_{i=0}^{n-1}y_i\right)-1\right),
--   $$
--   where $B_n$ is the ordinary box moment. Factorial coprimality allows the AP coefficients to be absorbed by invertible changes of coordinates.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/FaceMoments.lean#L248-L280

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

theorem Wikipedia.SzemeredisTheorem.mean_faceCenteredProduct_eq_boxMoment
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial n))
    (ν : ZMod N → ℝ) (j : Fin (n + 1)) :
    mean (faceCenteredProduct (n + 1) N ν j) =
      boxMoment n (fun y : Fin n → ZMod N =>
        ν (∑ i, y i) - 1) := by sorry
