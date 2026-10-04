-- Prove2me | Theorems.Thm_MovingSofa_volume_le_volume_gerversSofaWith
-- name    : MovingSofa.volume_le_volume_gerversSofaWith
-- status  : Open
-- author  : @Tamas Fulop
-- created : 2026-10-03T13:58:06.850515+00:00
-- url     : https://prove2.me/theorems/2bfbde15-360d-456f-8b1e-868a559c8c9c
-- title:
--   Every moving sofa is bounded by Gerver's area
-- statement:
--   Let $A,B,\varphi,\theta$ satisfy $\mathrm{ABphiThetaSpec}$ and let $s$ be any moving sofa. Then $$\mathrm{volume}(s)\le\mathrm{volume}(G(A,B,\varphi,\theta)).$$ This is the upper-bound half of Baek's Theorem 1.1; with the movability witness it composes to the supremum equality that is the mission goal.
-- source:
--   https://github.com/deancureton/MovingSofa/blob/4d5569131940815f47a9ccf3e90a4c5043c56127/MovingSofaSubmission/Challenge.lean#L125-L129 (upper-bound half of Baek arXiv:2411.19826 Thm 1.1)

import Definitions.Def_MovingSofa_Basic
open MovingSofa MeasureTheory
open scoped EuclideanGeometry Real ENNReal

namespace MovingSofa

theorem volume_le_volume_gerversSofaWith (A B phi theta : ℝ)
    (h : GerversSofa.ABphiThetaSpec A B phi theta) (s : Set ℝ²)
    (hs : ∃ m, IsMovingSofa s m) :
    volume s ≤ volume (gerversSofaWith A B phi theta) := by sorry

end MovingSofa
