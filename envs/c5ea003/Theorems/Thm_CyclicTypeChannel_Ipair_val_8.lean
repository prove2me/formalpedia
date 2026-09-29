-- Prove2me | Theorems.Thm_CyclicTypeChannel_Ipair_val_8
-- name    : CyclicTypeChannel.Ipair_val_8
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:29:20.564745+00:00
-- url     : https://prove2.me/theorems/60cbd731-712d-4e8f-a962-bbf749ea212e
-- title:
--   The `C8` type-pair channel.
-- statement:
--   **The `C8` type-pair channel.**
--
--   ```lean
--   theorem CyclicTypeChannel.Ipair_val_8: Ipair 8 = (21/16 : ℝ) := by sorry
--   /-! ### The abstract cyclic order `C9` -/
--
--
--
--
--
--   /-! ### The abstract cyclic order `C15` -/
--
--
--
--
--
--   /-! ### CRT additivity of the type-pair information
--
--   For coprime cyclic orders the information carried by the unordered type pair of
--   a semiprime splits as a sum over the primary components. -/
--
--
--
--
--
--   /-! ### Evenness, not compositeness, is what breaks the cap -/
--
--
--
--
--
--
--
--
--   /-! ### A value beyond the reach of enumeration
--
--   `n = 60` has a sample box of `3600` pairs, out of reach of direct kernel
--   enumeration; the CRT law computes it from the primary parts `4` and `15`. -/
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/CyclicTypeChannelCRT.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/CyclicTypeChannelCRT.lean#L251

-- Thm stub generated from Shared/CyclicTypeChannelCRT.lean
import Mathlib
import Definitions.Def_Shared_CyclicTypeChannel
import Definitions.Def_Shared_CyclicTypeChannelCRTLaw
/-
# CRT additivity of the cyclic type-pair channel

This file extends the exact-value catalogue of the cyclic type-pair channel to
the orders `n ∈ {3, 5, 8, 9, 15}` and proves the two structural laws that the
extended table makes visible.

* **CRT additivity.**  For coprime cyclic orders the type-pair information is
  *exactly additive*:
  `Ipair (n₁ * n₂) = Ipair n₁ + Ipair n₂` whenever `gcd n₁ n₂ = 1`
  (verified here for the pairs `(2,3)`, `(2,5)`, `(4,3)`, `(3,5)`).
  This is the information-theoretic shadow of the CRT decomposition of a cyclic
  group into its primary components.

* **Evenness, not compositeness, breaks the one-bit cap.**  The order `8` is a
  further above-cap example (`21/16 > 1`), while *every* odd order computed here
  (`3, 5, 9, 15`) sits strictly *below* one bit.  So the mechanism which pushes
  the multi-state type channel above the binary-fork cap is the presence of the
  order-two element (the quadratic character), amplified by the remaining
  divisor structure.
-/

open CyclicTypeChannel

open Finset

set_option maxRecDepth 100000

/-! ### The abstract cyclic order `C3` -/





/-! ### The abstract cyclic order `C5` -/





/-! ### The abstract cyclic order `C8` -/

theorem CyclicTypeChannel.Ipair_val_8: Ipair 8 = (21/16 : ℝ) := by sorry
