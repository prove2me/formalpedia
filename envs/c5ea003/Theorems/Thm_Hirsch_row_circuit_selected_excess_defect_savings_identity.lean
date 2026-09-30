-- Prove2me | Theorems.Thm_Hirsch_row_circuit_selected_excess_defect_savings_identity
-- name    : Hirsch.row_circuit_selected_excess_defect_savings_identity
-- status  : Proved
-- author  : @jjosh
-- created : 2026-09-11T19:45:41.674711+00:00
-- url     : https://prove2.me/theorems/c44c3313-11e2-49e0-aa41-b8acea36c29e
-- title:
--   Exact deletion-savings identity for a row-circuit common carrier
-- statement:
--   Let P={x in R^d : <a_i,x> <= b_i} be a bounded finite n-row H-polyhedron, let x be feasible, and suppose y-x is a row-circuit direction. For the canonical common carrier of x and y, let h be its coordinate dimension, E the original rows whose restrictions to the carrier are nonzero, Z the nonzero ambient rows neutral on y-x, and F any selected subset of E with |F|>=h. Let delta be the loss of neutral restricted rank after keeping only F∩Z. Then the ambient row excess n-d splits exactly into five nonnegative accounting terms: selected presentation excess |F|-h, neutral-rank defect delta, surplus row disappearance n+h-(|E|+d), omitted nonneutral effective rows |(E\F)\Z|, and omitted-neutral redundancy |(E\F)∩Z|-delta. Their sum is exactly n-d. Neither checkpoint is required to be a vertex. This is an exact one-carrier identity, not a graph-routing theorem.
-- source:
--   https://github.com/jjoshua2/prove2me-work/commit/ed33edd69aa9a25129b31a8448ef3303abb29b4e ; standalone Lean/Axiom gate Actions run 34639229285

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_circuit_model
import Definitions.Def_Hirsch_circuit_slack_model
import Definitions.Def_Hirsch_common_face_geometry
open scoped BigOperators RealInnerProductSpace InnerProduct
open Set Module Hirsch

namespace Hirsch
theorem row_circuit_selected_excess_defect_savings_identity
    {d n : ℕ}
    (a : Fin n → EuclideanSpace ℝ (Fin d)) (b : Fin n → ℝ)
    (x y : EuclideanSpace ℝ (Fin d))
    (hbd : Bornology.IsBounded (Hpoly a b)) (hx : x ∈ Hpoly a b)
    (hcirc : IsRowCircuit a (y - x))
    (F : Finset (Fin n))
    (hF : F ⊆ HirschCommonFace.commonFaceEffectiveRows a b x y)
    (hface : HirschCommonFace.commonFaceDim a b x y ≤ F.card) :
    let h := HirschCommonFace.commonFaceDim a b x y
    let E := HirschCommonFace.commonFaceEffectiveRows a b x y
    let Z := Finset.univ.filter (fun i => a i ≠ 0 ∧ ⟪a i, y - x⟫ = 0)
    let delta := (h - 1) -
      Module.finrank ℝ
        (((HirschCommonFace.rowEvalMap a (F ∩ Z)).domRestrict
          (HirschCommonFace.commonDirection a b x y)).range)
    (F.card - h) + delta +
      (n + h - (E.card + d)) +
      ((E \ F) \ Z).card + (((E \ F) ∩ Z).card - delta) = n - d := by sorry
end Hirsch
