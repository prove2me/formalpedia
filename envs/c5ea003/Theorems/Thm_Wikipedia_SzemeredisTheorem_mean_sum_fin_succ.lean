-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_sum_fin_succ
-- name    : Wikipedia.SzemeredisTheorem.mean_sum_fin_succ
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:57.248008+00:00
-- url     : https://prove2.me/theorems/50343dcd-8ceb-4e97-9e71-3e11c5298b5f
-- title:
--   A nonempty tuple sum is uniformly distributed
-- statement:
--   Let $G$ be a finite abelian group, let $n\ge0$ be an integer, and let $h:G\to\mathbb R$. Then
--   $$
--   \mathbb E_{x\in G^{n+1}}h\!\left(\sum_{i=0}^{n}x_i\right)=\mathbb E_{a\in G}h(a).
--   $$
--   Thus the sum of $n+1$ independent uniform coordinates is uniform on $G$. The tuple always has at least one coordinate.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Transference/CutDiscrepancy.lean#L240-L269

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Transference_CutDiscrepancy
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Cut discrepancy on finite additive groups

This file defines the deletion maps and cut-discrepancy relation used by the
Green--Tao transference argument.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.mean_sum_fin_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (h : G → ℝ) :
    mean (fun x : Fin (n + 1) → G => h (∑ i, x i)) = mean h := by sorry
