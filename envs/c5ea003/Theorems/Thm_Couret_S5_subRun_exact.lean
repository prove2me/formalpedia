-- Prove2me | Theorems.Thm_Couret_S5_subRun_exact
-- name    : Couret.S5.subRun_exact
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T20:25:26.585565+00:00
-- url     : https://prove2.me/theorems/4fd36f5b-a69e-43c0-b5f2-c690a173c5f6
-- title:
--   The subproduct-mask run exactly represents nonempty selections
-- statement:
--   Write $C=\mathbb Z/2\mathbb Z\times\mathbb Z/4\mathbb Z$, with residue map $\rho$ taking $(0,0),(0,1),(0,2),(0,3),(1,0),(1,1),(1,2),(1,3)$ to $1,7,19,13,11,17,29,23$, respectively. For every finite word $w$ over $C$, let $m(w)$ be its specified subproduct-mask run and $U(w)$ the set of products of nonempty position selections. Then
--
--   $$u\in\operatorname{supp}(m(w))\iff u\in U(w)\qquad(u\in C).$$
--
--   For the empty word both supports are empty.
-- source:
--   Alexandre Couret, Certified minimal memory for a divisor-residue presence observable modulo 30, https://zenodo.org/records/23989640; archive Couret_BC_MOD30_Companion_20261105.zip, SHA-256 9bb2678164c63a9e47c192093f5ce9deb1b7b74a1f1c8fecc77f305a408266a2; file source/S5/SubproductSemantics.lean, lines 62–71; source file SHA-256 ba13bc319dc0b6baacbd98ea26d1e89628af10edec99409e87d0f01ff3d4e21c; theorem Couret.S5.subRun_exact

import Definitions.Def_Couret_SubproductSemantics_e0771d3a736f
import Std
import Theorems.Thm_Couret_S5_selectedSupport_snoc
import Theorems.Thm_Couret_maskSupport_or
import Theorems.Thm_Couret_maskSupport_singleton
import Theorems.Thm_Couret_maskSupport_zero
import Theorems.Thm_Couret_shiftMask_support
import Definitions.Def_Couret_BCS5MaskSemantics_646df6f48a3c
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Couret
namespace S5

theorem subRun_exact (w : Word Code30) (u : Code30) :
    maskSupport (subRun w) u ↔ selectedSupport w u := by sorry


end S5
end Couret
