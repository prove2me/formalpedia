-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_weightedAPCount_of_denseAPCount
-- name    : Wikipedia.SzemeredisTheorem.weightedAPCount_of_denseAPCount
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:35:36.4414+00:00
-- url     : https://prove2.me/theorems/add2414b-bf08-4dab-ad8a-c631978d9efc
-- title:
--   A dense set-count bound gives a bounded-weight AP bound
-- statement:
--   Let $N\ne0$, $\delta\ge0$, and suppose the dense AP-count property in length $k$ holds at density $\delta/2$ with count bound $c$. Every function $g:\mathbb Z/N\mathbb Z\to[0,1]$ with mean at least $\delta$ then satisfies $(\delta/2)^k c\le\operatorname{cyclicAPCount}(k,N,g)$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Szemeredi/Weighted.lean#L42-L103

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Szemeredi_Weighted
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Fintype.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# From dense sets to bounded dense weights

The hypergraph-removal layer will first produce a quantitative progression
count for dense finite sets.  This file proves the standard thresholding
step that upgrades such a theorem to functions `g : ZMod N → [0,1]`.
-/
open Wikipedia.SzemeredisTheorem

theorem Wikipedia.SzemeredisTheorem.weightedAPCount_of_denseAPCount
    {k N : ℕ} [NeZero N] {δ c : ℝ}
    (hδ0 : 0 ≤ δ)
    (hdense : HasDenseAPCount k N (δ / 2) c)
    {g : ZMod N → ℝ}
    (hg0 : ∀ x, 0 ≤ g x)
    (hg1 : ∀ x, g x ≤ 1)
    (hmean : δ ≤ mean g) :
    (δ / 2) ^ k * c ≤ cyclicAPCount k N g := by sorry
