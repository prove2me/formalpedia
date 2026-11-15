-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_OrderedPattern_toWeighted_patternCount_eq
-- name    : Wikipedia.SzemeredisTheorem.OrderedPattern.toWeighted_patternCount_eq
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:34:50.042463+00:00
-- url     : https://prove2.me/theorems/cc1777ec-39f3-423c-83fb-a3ac1557fbf3
-- title:
--   A weighted pattern count is a normalized occurrence cardinality
-- statement:
--   For an ordered pattern $H$ on a finite nonempty type $G$ with decidable equality and parameters $k,r$, the pattern count of its indicator-weighted system equals $|H.\mathrm{occurrenceFinset}|/|G^k|$.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/OrderedPattern.lean#L313-L335

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
open Wikipedia.SzemeredisTheorem.OrderedPattern

theorem Wikipedia.SzemeredisTheorem.OrderedPattern.toWeighted_patternCount_eq
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : OrderedPattern G k r) :
    H.toWeighted.patternCount =
      (H.occurrenceFinset.card : ℝ) /
        Fintype.card (Fin k → G) := by sorry
