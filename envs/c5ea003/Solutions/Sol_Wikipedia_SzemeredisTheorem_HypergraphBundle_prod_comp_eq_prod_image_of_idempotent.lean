-- Prove2me | solution 1 for Wikipedia.SzemeredisTheorem.HypergraphBundle.prod_comp_eq_prod_image_of_idempotent
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-14T10:13:01.344345+00:00
-- url     : https://prove2.me/submissions/2472beb0-df61-4599-9b7c-ef1907540fe7

/- Mechanically transplanted from https://github.com/plby/lean-proofs.git at 8822f7ddef30fadbd92e1c6ab4ed897af356af5e. Original scopes and proof bytes are oracle-derived. -/
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Finite_Mean
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleCounting
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleDuplication
import Definitions.Def_GreenTaoPort_Wikipedia_SzemeredisTheorem_Hypergraph_HypergraphBundleIndicatorDuplication
import Mathlib.Algebra.BigOperators.Expect
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Indicator weights on a duplicated hypergraph bundle

The source-indexed doubled product retains both labelled copies of every
remaining occurrence edge.  The ordinary duplicated bundle instead stores
the image of the source-edge map, so it identifies the two copies of an edge
contained in the shared edge.  For pulled-back zero--one base weights this
identification does not change the product: the only lost multiplicity is a
repeated idempotent factor.
-/
open Wikipedia.SzemeredisTheorem
open scoped BigOperators
open Wikipedia.SzemeredisTheorem.HypergraphBundle
variable {J K G : Type*}
  [DecidableEq J] [DecidableEq K]
  {H : Finset (Finset J)}

open Wikipedia.SzemeredisTheorem.HypergraphBundle in
/-- A product is unchanged when its indexing map identifies factors whose
common value is idempotent. -/
theorem solution
    {α β M : Type*} [DecidableEq β]
    [CommMonoid M]
    (s : Finset α) (f : α → β) (w : β → M)
    (hw : ∀ b ∈ s.image f, w b * w b = w b) :
    (∏ a ∈ s, w (f a)) =
      ∏ b ∈ s.image f, w b := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hw' :
          ∀ b ∈ s.image f, w b * w b = w b := by
        intro b hb
        exact hw b (by
          rw [Finset.image_insert]
          exact Finset.mem_insert_of_mem hb)
      rw [Finset.prod_insert ha, ih hw',
        Finset.image_insert]
      by_cases hfa : f a ∈ s.image f
      · rw [Finset.insert_eq_of_mem hfa]
        calc
          w (f a) * ∏ b ∈ s.image f, w b =
              w (f a) *
                (w (f a) *
                  ∏ b ∈ (s.image f).erase (f a), w b) := by
            rw [Finset.mul_prod_erase (s.image f) w hfa]
          _ =
              w (f a) *
                ∏ b ∈ (s.image f).erase (f a), w b := by
            rw [← mul_assoc,
              hw (f a) (by
                rw [Finset.image_insert]
                exact Finset.mem_insert_self _ _)]
          _ = ∏ b ∈ s.image f, w b :=
            Finset.mul_prod_erase (s.image f) w hfa
      · rw [Finset.prod_insert hfa]
