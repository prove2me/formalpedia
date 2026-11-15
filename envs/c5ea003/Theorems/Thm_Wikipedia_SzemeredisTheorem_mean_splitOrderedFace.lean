-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_mean_splitOrderedFace
-- name    : Wikipedia.SzemeredisTheorem.mean_splitOrderedFace
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T10:14:57.016852+00:00
-- url     : https://prove2.me/theorems/e6e7790a-15c4-46df-be78-746f257b34a1
-- title:
--   Splitting a tuple mean along an ordered face
-- statement:
--   Let $G$ be finite, let $k,r$ be natural numbers, and let $e:\{0,\ldots,r-1\}\hookrightarrow\{0,\ldots,k-1\}$ be increasing. For $f:G^k\to\mathbb R$,
--   $$
--   \mathbb E_xf(x)=\mathbb E_{y\in G^r}\mathbb E_{z\in G^{\operatorname{im}(e)^c}}f(\operatorname{join}_e(y,z)).
--   $$
--   The joining map is the inverse of the coordinate-splitting equivalence: it places $y$ on the ordered face and $z$ on its complement. Nonemptiness of $G$ is not assumed.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedPattern.lean#L111-L135

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Complete ordered partite hypergraph patterns

Recursive hypergraph removal naturally produces lower-rank constraints on a
fixed collection of vertex classes.  It is convenient to index an ordered
rank-`r` face by an embedding `Fin r ↪ Fin k`.  This permits composition of
faces without quotienting by permutations.

This file defines weighted and unweighted complete ordered patterns, their
normalized occurrence counts, deletions, and the uniform removal property
used by the rank induction.  Rank zero is proved directly.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators

theorem Wikipedia.SzemeredisTheorem.mean_splitOrderedFace
    {G : Type*} [Fintype G] {k r : ℕ}
    (e : OrderedFace k r) (f : (Fin k → G) → ℝ) :
    mean f =
      mean₂ (fun y : Fin r → G =>
        fun z : OrderedFaceComplement e → G =>
          f ((splitOrderedFaceEquiv e).symm (y, z))) := by sorry
