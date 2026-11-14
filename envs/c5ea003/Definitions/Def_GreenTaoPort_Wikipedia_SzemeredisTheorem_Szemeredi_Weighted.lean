-- Prove2me | Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Szemeredi_Weighted
-- name    : GreenTaoPort_Wikipedia_SzemeredisTheorem_Szemeredi_Weighted
-- status  : Definition
-- author  : @kmehltretter82
-- created : 2026-11-14T05:50:30.405211+00:00
-- url     : https://prove2.me/theorems/ab8732c9-3a5c-45e5-a20b-e89021e9b313
-- title:
--   Dense-set and bounded-weight progression-count predicates
-- statement:
--   Fix a progression length $k$, a positive modulus $N$, and real parameters $\delta,c$. The dense-set counting predicate says that every finite set $A\subseteq\mathbb Z/N\mathbb Z$ with normalized density at least $\delta$ has normalized $k$-term progression count at least $c$.
--
--   The bounded-weight predicate replaces the indicator of $A$ by an arbitrary real function $g$ satisfying $0\le g\le1$ and $\operatorname{mean}(g)\ge\delta$, and requires the same lower bound $c$. Their uniform variants quantify over every positive natural modulus with the same $k,\delta,c$. The progression counts include zero common differences; positivity assumptions on the thresholds belong to later theorems.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Szemeredi/Weighted.lean#L14-L40

import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_ArithmeticProgression_Count
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
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

namespace Wikipedia.SzemeredisTheorem

/-- A quantitative dense-set arithmetic-progression counting statement at
one fixed modulus. -/
def HasDenseAPCount (k N : ℕ) [NeZero N]
    (δ c : ℝ) : Prop :=
  ∀ A : Finset (ZMod N),
    δ ≤ mean (finsetIndicator A) →
      c ≤ cyclicAPCount k N (finsetIndicator A)

/-- A quantitative arithmetic-progression counting statement for bounded
nonnegative weights at one fixed modulus. -/
def HasWeightedAPCount (k N : ℕ) [NeZero N]
    (δ c : ℝ) : Prop :=
  ∀ g : ZMod N → ℝ,
    (∀ x, 0 ≤ g x) →
    (∀ x, g x ≤ 1) →
    δ ≤ mean g →
      c ≤ cyclicAPCount k N g

/-- Uniform dense-set AP counting with one lower bound for every nontrivial
cyclic modulus. -/
def HasUniformDenseAPCount (k : ℕ) (δ c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N], HasDenseAPCount k N δ c

/-- Uniform bounded-weight AP counting with one lower bound for every
nontrivial cyclic modulus. -/
def HasUniformWeightedAPCount (k : ℕ) (δ c : ℝ) : Prop :=
  ∀ (N : ℕ) [NeZero N], HasWeightedAPCount k N δ c



end Wikipedia.SzemeredisTheorem


