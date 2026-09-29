-- Prove2me | Theorems.Thm_TropicalSatake_unique_top2Set_iff_exists_unique_bottom
-- name    : TropicalSatake.unique_top2Set_iff_exists_unique_bottom
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:21:41.752122+00:00
-- url     : https://prove2.me/theorems/29335214-7e69-423c-aa16-267b16753501
-- title:
--   Unique top2Set iff exists unique bottom
-- statement:
--   Formal statement of `TropicalSatake.unique_top2Set_iff_exists_unique_bottom` from the Aether Catalog (Bridges). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem TropicalSatake.unique_top2Set_iff_exists_unique_bottom(x : Fin 3 → ℝ) :
--       (∃! A : Finset (Fin 3), IsTop2Set x A) ↔
--       ∃! c : Fin 3, ∀ i : Fin 3, i ≠ c → x c < x i := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/TropicalSatakeTop2Margin.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/TropicalSatakeTop2Margin.lean#L74

-- Thm stub generated from Bridges/TropicalSatakeTop2Margin.lean
import Mathlib
import Definitions.Def_Bridges_TropicalSatakeTop2Margin
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Satake Top-2 Margin Theorem for GL₃ Hecke Score Classifiers

This file formalizes a sharp robustness theorem for top-2 label sets determined by
score triples `x : Fin 3 → ℝ`. The key results are:

1. **Unique top-2 set characterization**: A unique top-2 set exists iff there is a unique
   "bottom" class strictly below the other two.

2. **Perturbation stability**: If the minimum gap from the excluded class to the top-2 set
   exceeds `2ε`, then any coordinatewise `ε`-perturbation preserves the top-2 set.

3. **Sharp converse**: If one member of the top-2 set has margin at most `2ε` over the
   excluded class, then there exists an `ε`-perturbation destroying the top-2 set.

4. **Max-plus transfer**: For max-plus linear score models (tropical Satake reconstructions),
   test-family perturbation of size `η` induces score perturbation of size at most `η`,
   giving a concrete robustness certificate.

## Mathematical context

For GL₃ tropical Satake classifiers, scores are computed as max-plus linear forms on
a finite test family. The top-2 label set identifies the two most plausible classes.
Robustness of this label set under perturbation of the test valuations is the key
certification property. The sharp threshold is governed by the gap between the second
and third ordered scores—equivalently, the minimum separation between the excluded
class and the top-2 pair.
-/

open Finset

open TropicalSatake

/-! ## Core definitions -/



/-! ## Finite enumeration helpers for Fin 3 -/


/-
Any two-element subset of `Fin 3` has a unique complement element.
-/

/-! ## Section 1: Unique top-2 set characterization -/

/-
A unique top-2 set exists iff there is a unique bottom class strictly below
all others. This is the cleanest characterization for `Fin 3`.
-/

theorem TropicalSatake.unique_top2Set_iff_exists_unique_bottom(x : Fin 3 → ℝ) :
    (∃! A : Finset (Fin 3), IsTop2Set x A) ↔
    ∃! c : Fin 3, ∀ i : Fin 3, i ≠ c → x c < x i := by sorry
