-- Prove2me | Theorems.Thm_mme_regular_fiber_ratio_transfer
-- name    : mme_regular_fiber_ratio_transfer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:52:14.355774+00:00
-- url     : https://prove2.me/theorems/447badae-cdf3-45d9-bbdd-2a4fb2b8acbe
-- title:
--   Lossless transfer from total cardinality to regular fiber degree
-- statement:
--   Let an ambient finite family and a target finite family both be regular over the same nonempty set of possible vertices. If their respective total cardinalities factor as $W D_{\mathrm{amb}}$ and $W D_{\mathrm{tar}}$, with $W>0$, then every bound $|A|\leq\rho|T|$ transfers without loss to the common fiber degrees: $D_{\mathrm{amb}}\leq\rho D_{\mathrm{tar}}$. This cancellation principle is useful in laser-method pruning arguments, where a total completion bound must control local collision degrees.
-- source:
--   Elementary finite-cardinality cancellation lemma; formalized for the Stothers type-2 laser-method extraction.

import Mathlib

set_option autoImplicit false

theorem mme_regular_fiber_ratio_transfer
    {Edge : Type} [DecidableEq Edge]
    (ambient target : Finset Edge)
    (wordCount ambientDegree targetDegree : ℕ) (rho : ℝ)
    (hword : 0 < wordCount)
    (hambient : ambient.card = wordCount * ambientDegree)
    (htarget : target.card = wordCount * targetDegree)
    (hratio : (ambient.card : ℝ) ≤ rho * (target.card : ℝ)) :
    (ambientDegree : ℝ) ≤ rho * (targetDegree : ℝ) := by
  sorry
