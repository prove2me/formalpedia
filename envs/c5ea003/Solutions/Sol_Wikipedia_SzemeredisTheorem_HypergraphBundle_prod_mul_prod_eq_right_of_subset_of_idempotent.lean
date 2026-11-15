-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.prod_mul_prod_eq_right_of_subset_of_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:16:25.149462+00:00
-- url     : https://prove2.me/submissions/dd88145b-b609-4f1e-a457-08bd65dc00d7

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleFiltration
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleGeneralizedCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Generalized counting for closed hypergraph bundles

This file packages the part of Tao's generalized counting argument which
is specific to hypergraph bundles.

There are two points which are easy to lose in a scalar recurrence.

* The defect at a selected maximal edge is localized to the product of
  the strict-boundary indicators.  Since those indicators already occur
  among the remaining bundle factors, idempotence lets us insert that
  boundary product without changing the contribution.
* After Cauchy--Schwarz, all remaining maximal-rank indicator factors may
  be discarded.  The resulting moment is the count of the duplicated
  lower-order bundle.  Its main-density product contains one copy of the
  strict boundary and two copies of every other lower-order edge.

The last section records a flexible numerical envelope for the ensuing
double induction.  It deliberately separates the same-rank density floor
`α` from the all-rank density floor `μ`: the defect term only loses powers
of `α`, while the common frozen-uniformity error may lose powers of `μ`.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}
/-! ## Local strict-boundary products -/

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- If `s ⊆ t` and all factors on `s` are idempotent, multiplying the
`t`-product by the `s`-product does not change it. -/
theorem solution
    {ι : Type*}
    (s t : Finset ι) (f : ι → ℝ)
    (hst : s ⊆ t)
    (hf : ∀ i ∈ s, f i * f i = f i) :
    (∏ i ∈ s, f i) * (∏ i ∈ t, f i) =
      ∏ i ∈ t, f i := by
  classical
  induction s using Finset.induction_on generalizing t with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hat : a ∈ t :=
        hst (Finset.mem_insert_self a s)
      have hst' : s ⊆ t.erase a := by
        intro i hi
        exact Finset.mem_erase.mpr
          ⟨fun hia => ha (hia ▸ hi),
            hst (Finset.mem_insert_of_mem hi)⟩
      have hf' :
          ∀ i ∈ s, f i * f i = f i := by
        intro i hi
        exact hf i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha]
      rw [← Finset.mul_prod_erase t f hat]
      calc
        (f a * ∏ i ∈ s, f i) *
              (f a * ∏ i ∈ t.erase a, f i) =
            (f a * f a) *
              ((∏ i ∈ s, f i) *
                ∏ i ∈ t.erase a, f i) := by
          ring
        _ =
            f a *
              ((∏ i ∈ s, f i) *
                ∏ i ∈ t.erase a, f i) := by
          rw [hf a (Finset.mem_insert_self a s)]
        _ = f a * ∏ i ∈ t.erase a, f i := by
          rw [ih (t.erase a) hst' hf']
