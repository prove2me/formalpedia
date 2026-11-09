-- Prove2me | Theorems.Thm_Couret_InterIA_Cubic_rectangle_two_coordinates
-- name    : Couret.InterIA.Cubic.rectangle_two_coordinates
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T19:58:44.085798+00:00
-- url     : https://prove2.me/theorems/502c5e03-34f0-4fc5-82a1-bcc5969e6c05
-- title:
--   Two coordinates distinguish an injective rectangle
-- statement:
--   Let $H,U,V:I\to\mathbb R$ and define $R_{p,q}=H+pU+qV$ for $(p,q)\in\{0,1\}^2$. If these four functions are pairwise distinct, then there exist $z,w\in I$ such that
--
--   $$(p,q)\longmapsto (R_{p,q}(z),R_{p,q}(w))\text{ is injective}.$$
--
--   Thus two scalar evaluations distinguish every corner of the functional rectangle.
-- source:
--   Alexandre Couret, Cubic observations for four-point convolution reconstruction: universal two-coordinate bound and Lean proof archive, https://zenodo.org/records/23983731; archive Cubic_Observations_Lean_Archive_20261105.zip, SHA-256 7a118549d5729dbcfbfb20bd35fea7ebd91275b7bde61591d6bdda5c13b749ec; file formal/lean/RectangleProbes.lean, lines 20–85; source file SHA-256 2a9d979b50edf3a1856fc7ac02e8ea5dce341c04960af2e3dd959cf365aecc5c; theorem Couret.InterIA.Cubic.rectangle_two_coordinates

import Definitions.Def_Couret_RectangleProbes_c3e716b02120
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace Couret.InterIA.Cubic

theorem rectangle_two_coordinates {ι : Type*} (H U V : ι → ℝ)
    (hinj : Function.Injective (rectangle H U V)) :
    ∃ z w : ι, Function.Injective
      (fun p : Bool × Bool => (rectangle H U V p z, rectangle H U V p w)) := by sorry


end Couret.InterIA.Cubic
