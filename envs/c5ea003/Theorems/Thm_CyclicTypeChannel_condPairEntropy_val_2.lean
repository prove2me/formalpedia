-- Prove2me | Theorems.Thm_CyclicTypeChannel_condPairEntropy_val_2
-- name    : CyclicTypeChannel.condPairEntropy_val_2
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:27:53.484547+00:00
-- url     : https://prove2.me/theorems/df1a637d-edfc-4d01-ac86-94efd5b6e1c8
-- title:
--   Exact conditional entropy of the type pair given the residue of the product.
-- statement:
--   Exact conditional entropy of the type pair given the residue of the product.
--
--   ```lean
--   theorem CyclicTypeChannel.condPairEntropy_val_2: condPairEntropy 2 = (1/2 : ℝ) := by sorry
--
--   /-! ### The `C4` channel: `Q(ζ_5)` -/
--
--
--
--
--
--   /-! ### The `C6` channel: `Q(ζ_7)` -/
--
--
--
--
--
--   /-! ### The `C10` channel: `Q(ζ_11)` -/
--
--
--
--
--
--   /-! ### The `C12` channel: `Q(ζ_13)` -/
--
--
--
--
--
--   /-! ### The `C16` channel: `Q(ζ_17)` -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelValues.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelValues.lean#L37

-- Thm stub generated from Shared/CyclicTypeChannelValues.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
/-
# Exact values of the cyclic splitting-type channel

Exact, closed-form evaluations of the type channel `H(T)`, the semiprime
type-pair entropy `H(Π)`, the conditional entropy `H(Π | N mod f)` and the
type-pair channel `I_pair = H(Π) - (1/φ(f)) ∑_c H(Π_c)` for the cyclic groups
`C₂, C₄, C₆, C₁₀, C₁₂, C₁₆`, i.e. for the cyclotomic fields
`Q(ζ₃), Q(ζ₅), Q(ζ₇), Q(ζ₁₁), Q(ζ₁₃), Q(ζ₁₇)`.

Every value is obtained from the count form `uEnt_eq_countSum` of the entropy
together with a kernel-checked enumeration of the fibre cardinalities over the
unit group.
-/

open CyclicTypeChannel

open Finset

set_option maxRecDepth 100000

/-! ### The `C2` channel: `Q(ζ_3)` -/

theorem CyclicTypeChannel.condPairEntropy_val_2: condPairEntropy 2 = (1/2 : ℝ) := by sorry
