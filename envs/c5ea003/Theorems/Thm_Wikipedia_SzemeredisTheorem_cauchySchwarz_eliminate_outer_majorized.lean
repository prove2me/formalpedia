-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_cauchySchwarz_eliminate_outer_majorized
-- name    : Wikipedia.SzemeredisTheorem.cauchySchwarz_eliminate_outer_majorized
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:48:53.553207+00:00
-- url     : https://prove2.me/theorems/e8b7e818-502a-450b-9ad3-7610607aa3cd
-- title:
--   Cauchy–Schwarz eliminates an outer factor dominated by a majorant
-- statement:
--   For finite types $X,Y$, real functions $u,v$ on $X$, and a real function $F$ on $X\times Y$, assume $0\le u(x)\le v(x)$. Then
--
--   $$
--   \left(\mathbb E_{x,y}u(x)F(x,y)\right)^2
--   \le(\mathbb E_xv(x))
--   \mathbb E_{x,y_0,y_1}\bigl[v(x)F(x,y_0)F(x,y_1)\bigr].
--   $$
--
--   Neither finite type is required to be nonempty.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/GreenTao/Transference/WeightedStrongLinearFormsCS.lean#L90-L134

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Condition
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_LinearForms_Independence
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_BoxNorm
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_FaceMoments
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_StrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearForms
import Definitions.Def_GreenTaoPort_Wikipedia_GreenTao_Transference_WeightedStrongLinearFormsCS
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
# Repeated weighted Cauchy--Schwarz for strong linear forms

This file supplies the recursive analytic bridge which precedes the
algebraic endpoint in `WeightedStrongLinearForms`.

The recursion is the quantitative finite version of Conlon--Fox--Zhao,
Lemma 6.3.  A parameterized cut system consists of a possibly signed core
and one nonnegative factor for every deleted coordinate.  Each factor is
dominated by a designated majorant.  One Cauchy--Schwarz step

* removes the head factor;
* pays the normalized mean of its majorant;
* duplicates the head coordinate;
* pairs every remaining factor; and
* inserts the removed majorant into the new core.

After all coordinates have been processed, the core is the product of all
copies of the original centered factor together with exactly one copy of
each selected face majorant.  No pointwise bound on the majorants is used.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
universe u
/-! ## Weighted finite Cauchy--Schwarz -/

theorem Wikipedia.SzemeredisTheorem.cauchySchwarz_eliminate_outer_majorized
    {X Y : Type*} [Fintype X] [Fintype Y]
    (u v : X → ℝ) (F : X → Y → ℝ)
    (hu : ∀ x, 0 ≤ u x)
    (huv : ∀ x, u x ≤ v x) :
    mean₂ (fun x y => u x * F x y) ^ 2 ≤
      mean v *
        mean₂ (fun x => fun p : Y × Y =>
          v x * F x p.1 * F x p.2) := by sorry
