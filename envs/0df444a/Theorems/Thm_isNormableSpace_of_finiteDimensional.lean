-- Prove2me | Theorems.Thm_isNormableSpace_of_finiteDimensional
-- name    : isNormableSpace_of_finiteDimensional
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T01:52:30.540784+00:00
-- url     : https://prove2.me/theorems/0618d0f4-127f-4699-8155-7ef8836ae882
-- title:
--   is Normable Space of finite Dimensional: is Normable Space of finite Dimensional
-- statement:
--   A finite dimensional topological vector space over a complete normed field is normable.
--
--   Not registered as a global instance only for performance reasons. Separately attributed Apache-2.0 Mathlib compatibility backport at commit 9d581dfff2e41de989072ea63abf3daf69311520; target API and same-field transport specializations are explicit in the checked statement.
--
--   Source: https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Topology/Algebra/Module/FiniteDimension.lean
-- source:
--   https://github.com/leanprover-community/mathlib4/blob/9d581dfff2e41de989072ea63abf3daf69311520/Mathlib/Topology/Algebra/Module/FiniteDimension.lean

import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Definitions.Def_ImportCompatibility_Normability
set_option autoImplicit true
open Topology
variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E]

theorem isNormableSpace_of_finiteDimensional [FiniteDimensional 𝕜 E] : IsNormableSpace 𝕜 E := by sorry
