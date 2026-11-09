-- Prove2me | Theorems.Thm_Couret_S5_selectedSupport_snoc
-- name    : Couret.S5.selectedSupport_snoc
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:16:13.554528+00:00
-- url     : https://prove2.me/theorems/82f9394b-ce50-494f-8397-b8706c08014f
-- title:
--   Appending one factor updates nonempty subproduct support
-- statement:
--   Write $C=\mathbb Z/2\mathbb Z\times\mathbb Z/4\mathbb Z$, with residue map $\rho$ taking $(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)$ to $1,7,19,13,11,17,29,23$, respectively. Let $w$ be a finite word over $C$, let $g,u\in C$, and write $U(w)$ for products of nonempty selections of positions. Then
--
--   $$u\in U(wg)\iff u\in U(w)\ \lor\ (\exists v\in U(w),gv=u)\ \lor\ u=g.$$
--
--   The identity residue is included only when realized by a nonempty selection; the word $w$ may be empty.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/SubproductSemantics.lean, lines 36–60; source file SHA-256 ba13bc319dc0b6baacbd98ea26d1e89628af10edec99409e87d0f01ff3d4e21c; theorem Couret.S5.selectedSupport_snoc

import Definitions.Def_Couret_SubproductSemantics_e0771d3a736f
import Std
import Theorems.Thm_Couret_Choice_eval_allSkip
import Theorems.Thm_Couret_Choice_eval_of_not_picked
import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem selectedSupport_snoc (w : Word Code30) (g u : Code30) :
    selectedSupport (.snoc w g) u ↔
      selectedSupport w u ∨ (∃ v, selectedSupport w v ∧ mul30 g v = u) ∨ u = g := by sorry




end S5
end Couret
