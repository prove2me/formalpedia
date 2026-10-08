-- Prove2me | Theorems.Thm_ProofsInTheBook_Chapter20_squareBoundaryVertexChainRGCount_odd_of_side_colors
-- name    : ProofsInTheBook.Chapter20.squareBoundaryVertexChainRGCount_odd_of_side_colors
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-09-12T17:46:49.679413+00:00
-- url     : https://prove2.me/theorems/fa43b483-2878-4a15-b02e-18af14a5dd64
-- title:
--   Side-color constraints force odd boundary red–green count
-- statement:
--   Let A be any type with a map to the three colors red, green, blue. Choose four lists B,R,T,L and four corner elements $c_{00},c_{10},c_{11},c_{01}$ colored red, green, green, blue respectively. Require every entry of B to be red or green, every entry of R and T to be green or blue, and every entry of L to be red or blue. Form consecutive-edge lists along the chains $(c_{00},B,c_{10})$, $(c_{10},R,c_{11})$, $(c_{11},T,c_{01})$, and $(c_{01},L,c_{00})$, then concatenate them. The number of red–green edges in that list, counted with occurrence multiplicity, is odd. The lists need not be geometrically embedded or free of repetitions; no finiteness assumption on A or dissection data is required.
-- source:
--   Original declaration: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter20.lean#L1103. Repository topic: Monsky’s theorem, “One square and an odd number of triangles.”

import Init
import Mathlib
import Definitions.Def_P2MAssembly_Chapter20
set_option autoImplicit true
open ProofsInTheBook.Chapter20
open IsLocalRing
open MonskyColor

theorem ProofsInTheBook.Chapter20.squareBoundaryVertexChainRGCount_odd_of_side_colors {α : Type*}
    (bottom right top left : List α) (bottomLeft bottomRight topRight topLeft : α)
    (color : α → MonskyColor)
    (hbottomLeft : color bottomLeft = red)
    (hbottomRight : color bottomRight = green)
    (htopRight : color topRight = green)
    (htopLeft : color topLeft = blue)
    (hbottom : ∀ v ∈ bottom, colorIsRedGreen (color v))
    (hright : ∀ v ∈ right, colorIsGreenBlue (color v))
    (htop : ∀ v ∈ top, colorIsGreenBlue (color v))
    (hleft : ∀ v ∈ left, colorIsRedBlue (color v)) :
    Odd (listEdgeRGCount
      (squareBoundaryEdgeList bottom right top left bottomLeft bottomRight topRight topLeft)
      color) := by sorry
