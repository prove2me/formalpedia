-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_faceCenteredProduct_insertNth
-- name    : Wikipedia.SzemeredisTheorem.faceCenteredProduct_insertNth
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:04:09.049773+00:00
-- url     : https://prove2.me/theorems/1d8e0c78-4de6-49a9-9066-affadfece429
-- title:
--   A centered face product is a weighted deleted-coordinate cube product
-- statement:
--   For natural $n,N$, a real function $\nu$ on $\mathbb Z/N\mathbb Z$, distinguished coordinate $j$, inserted Boolean pair $a$, and doubled deleted-coordinate tuple $y$, the centered face product equals $\prod_{\omega\in\{0,1\}^n}(\nu(\sum_t(j.\mathrm{succAbove}(t)-j)y_t(\omega_t))-1)$, with coefficients interpreted modulo $N$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/FaceMoments.lean#L143-L169

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

theorem Wikipedia.SzemeredisTheorem.faceCenteredProduct_insertNth
    (n N : ℕ) (ν : ZMod N → ℝ)
    (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (y : Fin n → Bool → ZMod N) :
    faceCenteredProduct (n + 1) N ν j
        (Fin.insertNth j a y) =
      ∏ ω : Fin n → Bool,
        (ν (∑ t : Fin n,
          ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
            ZMod N) * y t (ω t))) - 1) := by sorry
