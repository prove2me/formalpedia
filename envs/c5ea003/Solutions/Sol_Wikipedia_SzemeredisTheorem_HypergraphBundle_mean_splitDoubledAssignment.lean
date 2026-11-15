-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.mean_splitDoubledAssignment
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:04:44.478107+00:00
-- url     : https://prove2.me/submissions/aecb3083-efb2-4fc7-87f7-bd25946f9df2

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
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
# Duplicating the variables outside one bundle edge

The squared remainder in the bundle counting argument identifies the
variables on a selected edge `g₀` and takes two independent copies of every
variable outside `g₀`.  This file realizes that operation as a finite
hypergraph bundle.

An occurrence vertex in the doubled bundle is either a shared vertex of
`g₀`, or an outside vertex together with a Boolean copy label.  Every
remaining occurrence edge is lifted once into each copy.  The lift is
injective, preserves edge cardinality and projected base edges, and
therefore produces another valid bundle over the same base hypergraph.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- Fubini decomposition for the doubled occurrence variables. -/
theorem solution
    [Fintype K] [Fintype G]
    (g₀ : Finset K)
    (f : (DoubledOccurrenceVertex g₀ → G) → ℝ) :
    mean f =
      mean₂ (fun y : {v : K // v ∈ g₀} → G =>
        fun z :
          (EdgeComplement g₀ → G) ×
            (EdgeComplement g₀ → G) =>
          f (doubledAssignment g₀ y z)) := by
  calc
    mean f =
        mean (fun p :
          ({v : K // v ∈ g₀} → G) ×
            ((EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G)) =>
          f ((splitDoubledAssignmentEquiv g₀).symm p)) := by
      unfold mean
      apply Fintype.expect_equiv
        (splitDoubledAssignmentEquiv g₀)
      intro x
      simp
    _ = _ := by
      change
        mean (fun p :
          ({v : K // v ∈ g₀} → G) ×
            ((EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G)) =>
          f (doubledAssignment g₀ p.1 p.2)) =
        _
      exact
        mean_prod_type
          (fun y : {v : K // v ∈ g₀} → G =>
            fun z :
              (EdgeComplement g₀ → G) ×
              (EdgeComplement g₀ → G) =>
              f (doubledAssignment g₀ y z))
