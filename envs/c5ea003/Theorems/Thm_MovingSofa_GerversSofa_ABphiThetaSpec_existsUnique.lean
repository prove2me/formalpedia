-- Prove2me | Theorems.Thm_MovingSofa_GerversSofa_ABphiThetaSpec_existsUnique
-- name    : MovingSofa.GerversSofa.ABphiThetaSpec.existsUnique
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-09-29T18:43:41.324095+00:00
-- url     : https://prove2.me/theorems/93d74877-a2f6-4c22-9ac1-9457b6fc81aa
-- title:
--   Existence and uniqueness of Gerver's constants
-- statement:
--   Let $A,B,\varphi,\theta$ be real numbers satisfying **ABphiThetaSpec**: $0\le\varphi\le\theta\le\pi/4$, $0\le A$, $0\le B$, and Romik's four equations (1)-(4). Then\n\n$$\exists!\,(A,B,\varphi,\theta),\quad \mathrm{ABphiThetaSpec}(A,B,\varphi,\theta).$$\n\nThere is exactly one quadruple on the closed domain satisfying the spec. This is Gerver's Theorem 2 in exact form and supplies the constants from which Gerver's sofa is built.\n\n**Formalization Note** Lean uses ASCII `ABphiThetaSpec` for the source `AB\u03c6\u03b8Spec`; the statement is otherwise verbatim.
-- source:
--   Romik 2018 eqs. (1)-(4); Gerver 1992 Thm 2; https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofaSubmission/Challenge.lean#L70-L82

import Definitions.Def_MovingSofa_Basic
open MovingSofa
open scoped EuclideanGeometry Real

namespace MovingSofa

namespace GerversSofa

theorem ABphiThetaSpec.existsUnique : ∃! ABphiTheta : ℝ × ℝ × ℝ × ℝ, ABphiThetaSpec ABphiTheta.1 ABphiTheta.2.1 ABphiTheta.2.2.1 ABphiTheta.2.2.2 := by sorry

end GerversSofa

end MovingSofa
