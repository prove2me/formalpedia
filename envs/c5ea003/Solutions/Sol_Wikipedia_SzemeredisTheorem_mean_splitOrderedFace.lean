-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.mean_splitOrderedFace
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:15:16.86514+00:00
-- url     : https://prove2.me/submissions/dec1512f-a688-4437-b5fe-a8d45d6f7f20

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_OrderedPattern
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3

section


/-!
# Products of independent finite means

The product of normalized averages over independent finite variables is the
normalized average over their product space.  This is the finite-probability
Fubini identity used when expanding products of generalized convolutions.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A normalized mean over a product type is the corresponding iterated
normalized mean. -/
theorem mean_prod_type
    {α β : Type*} [Fintype α] [Fintype β]
    (F : α → β → ℝ) :
    mean (fun p : α × β => F p.1 p.2) = mean₂ F := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) F)





end Wikipedia.SzemeredisTheorem

end
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

open Wikipedia.SzemeredisTheorem in
/-- Fubini decomposition of a full-tuple mean into an ordered face and its
complement. -/
theorem solution
    {G : Type*} [Fintype G] {k r : ℕ}
    (e : OrderedFace k r) (f : (Fin k → G) → ℝ) :
    mean f =
      mean₂ (fun y : Fin r → G =>
        fun z : OrderedFaceComplement e → G =>
          f ((splitOrderedFaceEquiv e).symm (y, z))) := by
  calc
    mean f =
        mean (fun p :
          (Fin r → G) × (OrderedFaceComplement e → G) =>
            f ((splitOrderedFaceEquiv e).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv
        (splitOrderedFaceEquiv e)
      intro x
      simp
    _ = _ := by
      simpa only [Prod.eta] using
        (mean_prod_type
          (fun y : Fin r → G =>
            fun z : OrderedFaceComplement e → G =>
              f ((splitOrderedFaceEquiv e).symm (y, z))))
