-- Prove2me | Definitions.Def_Novelty_OrderParameter
-- name    : Novelty_OrderParameter
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:34:36.510778+00:00
-- url     : https://prove2.me/theorems/70af74b5-fb15-4ad5-8963-d84a0cafb08c
-- title:
--   Aether Catalog definitions — Novelty_OrderParameter
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.OrderParameter`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/OrderParameter.lean by skeleton subtraction
import Mathlib

/-!
# Proof Space II: The order parameter and asymptotic incompleteness

The *order parameter* of proof space is the fraction of statements of length
`≤ n` that are provable:

  `r n = prov n / tot n`.

We work with abstract real-valued counting functions `prov, tot : ℕ → ℝ`, where
`tot` grows like `k ^ n` (the full proof space) and `prov` counts the provable
statements.

The main result, `orderParameter_tendsto_zero`, is an *asymptotic
incompleteness* statement: if the provable statements are exponentially sparse —
growing with a base `a` strictly smaller than the alphabet size `k` — then the
order parameter tends to `0`.  In words: **almost every statement is
unprovable.**  This is the "disordered phase" of proof space, the analogue of a
system sitting below its critical point.
-/

namespace ProofSpace

open Filter Topology

/-- The order parameter: fraction of length-`≤ n` statements that are provable. -/
noncomputable def orderParameter (prov tot : ℕ → ℝ) (n : ℕ) : ℝ := prov n / tot n



end ProofSpace


