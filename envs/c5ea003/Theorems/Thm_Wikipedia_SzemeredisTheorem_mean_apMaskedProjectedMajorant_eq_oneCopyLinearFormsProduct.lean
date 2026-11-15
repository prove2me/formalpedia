-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_apMaskedProjectedMajorant_eq_oneCopyLinearFormsProduct
-- name    : Wikipedia.SzemeredisTheorem.mean_apMaskedProjectedMajorant_eq_oneCopyLinearFormsProduct
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:35.301511+00:00
-- url     : https://prove2.me/theorems/33c6a65b-d8fa-463e-b6f8-8b872884fc66
-- title:
--   First moment of a masked projected majorant
-- statement:
--   Let $n\ge0$ and $N\ge1$ be integers, let $\nu:\mathbb Z/N\mathbb Z\to\mathbb R$, let $a:\{0,\ldots,n\}\to\{0,1\}$ be an active-face mask, and choose $j\in\{0,\ldots,n\}$. Denote the associated masked projected majorant by $M_{\nu,a,j}$ and its one-copy selected CFZ exponent by $e_1(n,a,j)$. Then
--   $$
--   \mathbb E_y M_{\nu,a,j}(y)=\mathbb E_x L_{n+1,\nu,e_1(n,a,j)}(x),
--   $$
--   where $L$ is the selected linear-forms product. This identifies the first moment as an explicit one-copy subproduct, with no nonnegativity assumption on $\nu$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/RecursiveRelativeSimplex.lean#L312-L365

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_Densification
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_ProjectedMajorantExpansion
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RecursiveRelativeSimplex
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_RelativeSimplexIteration
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
# Mixed projected moments for recursive relative densification

After one colour has been densified, its majorant is the constant function
one.  At the next stage the projected majorant is therefore not the product
of a common `ν` on every incident colour: it is a mixed product, with `ν`
only on the colours which remain sparse and `1` on the colours already
densified.

This file closes that moment gap.  A Boolean mask records the remaining
sparse colours.  We expand the first and second moments of the corresponding
projected majorant as explicit subproducts of the original CFZ linear-forms
system.  Consequently one unchanged `HasLinearFormsCondition` supplies the
moment package for every recursive mask, and hence supplies the next
heterogeneous full-to-projected state transition.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
/-! ## Majorants with previously densified colours set to one -/
/-! ## Masked CFZ selectors -/
/-! ## Exact mixed projected moments -/

theorem Wikipedia.SzemeredisTheorem.mean_apMaskedProjectedMajorant_eq_oneCopyLinearFormsProduct
    (n N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ)
    (active : Fin (n + 1) → Bool)
    (j : Fin (n + 1)) :
    mean (apMaskedProjectedMajorant n N ν active j) =
      mean (linearFormsProduct (n + 1) N ν
        (apMaskedProjectedOneCopyExponent n active j)) := by sorry
