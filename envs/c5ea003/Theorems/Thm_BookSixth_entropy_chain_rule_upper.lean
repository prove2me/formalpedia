-- Prove2me | Theorems.Thm_BookSixth_entropy_chain_rule_upper
-- name    : BookSixth.entropy_chain_rule_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-18T08:03:32.713888+00:00
-- url     : https://prove2.me/theorems/3bdf52fb-45f0-4227-aff5-02f72011d3b3
-- title:
--   Chapter 37 adapter: entropy chain-rule upper step
-- statement:
--   Chain-rule upper step: joint entropy is at most marginal entropy plus log of the second support size. Per-row Jensen plus marginal recombination for the Bregman-Minc entropy route.
-- source:
--   Aigner and Ziegler, Proofs from THE BOOK, Sixth Edition (2018), Chapter 37, chain-rule step for the entropy route to Bregman-Minc, p. 266. https://doi.org/10.1007/978-3-662-57265-8_37

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.entropy_chain_rule_upper (α β : Type*) [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (p : α × β → ℝ) (hnn : ∀ x, 0 ≤ p x) (hsum : ∑ x, p x = 1) :
    -∑ x, p x * Real.log (p x)
      ≤ -(∑ a, (∑ b, p (a, b)) * Real.log (∑ b, p (a, b))) + Real.log (Fintype.card β) := by sorry
