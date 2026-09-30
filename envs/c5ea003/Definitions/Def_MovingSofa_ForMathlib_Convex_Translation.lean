-- Prove2me | Definitions.Def_MovingSofa_ForMathlib_Convex_Translation
-- name    : MovingSofa_ForMathlib_Convex_Translation
-- status  : Definition
-- author  : @Tamas Fulop
-- created : 2026-09-29T22:33:43.451291+00:00
-- url     : https://prove2.me/theorems/5a895c53-0eca-403e-85e6-0667eb130ee8
-- title:
--   Translation of a convex body
-- statement:
--   Let $E$ be a real normed space and $K$ a convex body (nonempty compact convex set). For $v\in E$, the translate $K+v=\{p+v:p\in K\}$ is again a convex body. This bundles the translated carrier with convexity, compactness, and nonemptiness for reuse in cap/tail constructions.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofa/ForMathlib/Convex/Translation.lean#L4-L9

import Mathlib.Analysis.Convex.Body

set_option autoImplicit false

/-- Translation of a convex body by a vector. -/
def ConvexBody.translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : ConvexBody E) (v : E) : ConvexBody E where
  carrier := (fun p ↦ p + v) '' (K : Set E)
  convex' := by simpa only [add_comm] using K.convex.translate v
  isCompact' := K.isCompact.image (continuous_id.add continuous_const)
  nonempty' := K.nonempty.image _


