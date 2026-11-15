-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_insertNth
-- name    : Wikipedia.SzemeredisTheorem.mean_insertNth
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:12.764923+00:00
-- url     : https://prove2.me/theorems/d997a8f1-c056-4f2e-8019-a4046355beb0
-- title:
--   Averaging at any designated tuple coordinate
-- statement:
--   Let $G$ be finite, let $n\ge0$ be an integer, let $j\in\{0,\ldots,n\}$, and let $F:G^{n+1}\to\mathbb R$. If $\operatorname{ins}_j(a,y)$ inserts $a$ at position $j$ of the $n$-tuple $y$, then
--   $$
--   \mathbb E_xF(x)=\mathbb E_{a\in G}\mathbb E_{y\in G^n}F(\operatorname{ins}_j(a,y)).
--   $$
--   The coordinate may be chosen arbitrarily; the normalized-mean statement does not assume that $G$ is nonempty.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/APSimplexCut.lean#L200-L225

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_APCorrespondence
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_Simplex
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_LinearForms_Basic
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_APCut
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutTransport
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_SimplexTelescoping
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
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
# Cut control of arithmetic-progression simplex counts

For one edge in the arithmetic-progression simplex, the remaining edge
weights form a product of deleted-coordinate cut tests.  The distinguished
edge is an automorphic weighted sum when the modulus is coprime to the
relevant factorial.  This file makes that reduction exact and then applies
cut discrepancy edge by edge.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.mean_insertNth
    {G : Type*} [Fintype G] (n : ℕ)
    (j : Fin (n + 1)) (F : (Fin (n + 1) → G) → ℝ) :
    mean F =
      mean₂ (fun a : G => fun y : Fin n → G =>
        F (Fin.insertNth j a y)) := by sorry
