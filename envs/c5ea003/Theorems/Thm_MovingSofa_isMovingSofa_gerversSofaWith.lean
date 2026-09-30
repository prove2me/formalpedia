-- Prove2me | Theorems.Thm_MovingSofa_isMovingSofa_gerversSofaWith
-- name    : MovingSofa.isMovingSofa_gerversSofaWith
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-09-29T18:49:16.634567+00:00
-- url     : https://prove2.me/theorems/0bcdd849-1319-4e5d-bac6-00b2cf2cb7cb
-- title:
--   Gerver's sofa is a moving sofa
-- statement:
--   Let $A,B,\varphi,\theta$ satisfy $\mathrm{ABphiThetaSpec}$ and let $\mathrm{gerversSofaWith}(A,B,\varphi,\theta)$ be the sofa built from the rotation path $p(A,B,\varphi,\theta)$. Then\n\n$$\exists\,m,\quad \mathrm{IsMovingSofa}(\mathrm{gerversSofaWith}(A,B,\varphi,\theta),m).$$\n\nIn words: every Gerver parameter choice admits a continuous hallway motion, so the shape is itself a moving sofa and witnesses that the sofa constant is attained.\n\n**Formalization Note** The source states this for the chosen constants; here the constants are explicit arguments to keep definitions independent of the existence proof. Given uniqueness this implies the source form.
-- source:
--   Gerver 1992 Thm 2 (movability); https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofaSubmission/Challenge.lean#L115-L118

import Definitions.Def_MovingSofa_Basic
open MovingSofa
open scoped EuclideanGeometry Real

namespace MovingSofa

theorem isMovingSofa_gerversSofaWith (A B phi theta : ℝ) (h : GerversSofa.ABphiThetaSpec A B phi theta) : ∃ m, IsMovingSofa (gerversSofaWith A B phi theta) m := by sorry

end MovingSofa
