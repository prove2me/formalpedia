-- Prove2me | Theorems.Thm_CyclicTypeChannel_Ipair_val_2
-- name    : CyclicTypeChannel.Ipair_val_2
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:28:38.316746+00:00
-- url     : https://prove2.me/theorems/5417a522-dd9c-403a-9c63-a1980b5b6063
-- title:
--   The `C2` type-pair channel.
-- statement:
--   **The `C2` type-pair channel.**
--
--   ```lean
--   theorem CyclicTypeChannel.Ipair_val_2: Ipair 2 = (1 : ℝ) := by sorry
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
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelValues.lean#L60

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

theorem CyclicTypeChannel.Ipair_val_2: Ipair 2 = (1 : ℝ) := by sorry
