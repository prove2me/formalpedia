-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_apLinearForm_insertNth_deletedCubeEquiv
-- name    : Wikipedia.SzemeredisTheorem.apLinearForm_insertNth_deletedCubeEquiv
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:40:40.424918+00:00
-- url     : https://prove2.me/theorems/a368e63a-b7f3-496f-b505-1fb620f06e89
-- title:
--   An AP face form becomes a weighted deleted-coordinate sum
-- statement:
--   For natural $n,N$, distinguished coordinate $j\in\mathrm{Fin}(n+1)$, inserted Boolean pair $a$, doubled deleted-coordinate tuple $y$, and Boolean vertex $\omega$, the AP linear form on the tuple obtained by inserting $a$ at $j$ equals $\sum_t(j.\mathrm{succAbove}(t)-j)y_t(\omega_t)$ in $\mathbb Z/N\mathbb Z$, using the canonical deleted-cube reindexing.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/FaceMoments.lean#L117-L141

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

theorem Wikipedia.SzemeredisTheorem.apLinearForm_insertNth_deletedCubeEquiv
    (n N : ℕ) (j : Fin (n + 1))
    (a : Bool → ZMod N)
    (y : Fin n → Bool → ZMod N)
    (ω : Fin n → Bool) :
    apLinearForm (n + 1) N j (deletedCubeEquiv j ω)
        (Fin.insertNth j a y) =
      ∑ t : Fin n,
        ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
          ZMod N) * y t (ω t)) := by sorry
