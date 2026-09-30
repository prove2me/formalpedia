-- Prove2me | Theorems.Thm_MovingSofa_sofaConstant_eq_volume_gerversSofaWith
-- name    : MovingSofa.sofaConstant_eq_volume_gerversSofaWith
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-09-29T18:54:30.227393+00:00
-- url     : https://prove2.me/theorems/f791e8fb-4a22-4781-8859-f258f1e00995
-- title:
--   Optimality of Gerver's sofa
-- statement:
--   Let $A,B,\varphi,\theta$ satisfy $\mathrm{ABphiThetaSpec}$ and write $G(A,B,\varphi,\theta)$ for the associated Gerver sofa. Let $\mathrm{sofaConstant}$ be the supremum of $\mathrm{volume}(s)$ over all moving sofas $s$. Then\n\n$$\mathrm{sofaConstant} = \mathrm{volume}(G(A,B,\varphi,\theta)).$$\n\nThis is Baek's Theorem 1.1 (arXiv:2411.19826): Gerver's shape has maximal area among all shapes that can be moved around the corner, and the supremum is attained.\n\n**Formalization Note** Volumes use `MeasureSpace.volume`; the supremum is in $\mathbb{R}_{\ge 0}\cup\{\infty\}$ and is proved finite in the source development.
-- source:
--   Baek arXiv:2411.19826 Thm 1.1; https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofaSubmission/Challenge.lean#L125-L129

import Definitions.Def_MovingSofa_Basic
open MovingSofa MeasureTheory
open scoped EuclideanGeometry Real ENNReal

namespace MovingSofa

theorem sofaConstant_eq_volume_gerversSofaWith (A B phi theta : ℝ) (h : GerversSofa.ABphiThetaSpec A B phi theta) : sofaConstant = volume (gerversSofaWith A B phi theta) := by sorry

end MovingSofa
