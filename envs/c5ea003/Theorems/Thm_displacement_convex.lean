-- Prove2me | Theorems.Thm_displacement_convex
-- name    : displacement_convex
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-12T11:02:37.403556+00:00
-- url     : https://prove2.me/theorems/f5294a48-7f86-48b5-83ba-a2fee9d06aa5
-- title:
--   Displacement convex
-- statement:
--   Formal statement of `displacement_convex` from the Aether Catalog (Algebra). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem displacement_convex: ConvexOn ℝ (Set.Ioi 0) (fun x => d_oi x - x) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Algebra/OISCC/OrbitIteration.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Algebra/OISCC/OrbitIteration.lean#L98

-- Thm stub generated from Algebra/OISCC/OrbitIteration.lean
import Mathlib
import Definitions.Def_Algebra_OISCC_OrbitIteration

/-! # CatalogBuild.Speculative.OISCC.OrbitIteration

Auto-generated from theorem catalog database.
Domain: Speculative/OISCC
Declarations: 16
-/

noncomputable section

theorem displacement_convex: ConvexOn ℝ (Set.Ioi 0) (fun x => d_oi x - x) := by sorry
