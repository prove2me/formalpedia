-- Prove2me | Theorems.Thm_Wikipedia_SzemeredisTheorem_HypergraphBundle_prod_comp_eq_prod_image_of_idempotent
-- name    : Wikipedia.SzemeredisTheorem.HypergraphBundle.prod_comp_eq_prod_image_of_idempotent
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-14T09:33:24.953731+00:00
-- url     : https://prove2.me/theorems/9fb08042-66f3-4e36-b6d8-0a630d8792b6
-- title:
--   Idempotent factors permit passage to an image index set
-- statement:
--   Let $M$ be a commutative monoid, let $s$ be a finite set, and let $f$ map its index type to a type with decidable equality. If $w(b)^2=w(b)$ for every $b\in f(s)$, then $\prod_{a\in s}w(f(a))=\prod_{b\in f(s)}w(b)$, even when $f$ is not injective.
-- source:
--   https://github.com/plby/lean-proofs/blob/8822f7ddef30fadbd92e1c6ab4ed897af356af5e/src/latest/Wikipedia/SzemeredisTheorem/Hypergraph/HypergraphBundleIndicatorDuplication.lean#L72-L111

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

theorem Wikipedia.SzemeredisTheorem.HypergraphBundle.prod_comp_eq_prod_image_of_idempotent
    {α β M : Type*} [DecidableEq β]
    [CommMonoid M]
    (s : Finset α) (f : α → β) (w : β → M)
    (hw : ∀ b ∈ s.image f, w b * w b = w b) :
    (∏ a ∈ s, w (f a)) =
      ∏ b ∈ s.image f, w b := by sorry
