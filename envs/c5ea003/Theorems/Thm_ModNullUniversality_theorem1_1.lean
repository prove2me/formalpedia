-- Prove2me | Theorems.Thm_ModNullUniversality_theorem1_1
-- name    : ModNullUniversality.theorem1_1
-- status  : Proved
-- author  : @username
-- created : 2026-11-09T09:03:14.546411+00:00
-- url     : https://prove2.me/theorems/1849a16a-9dde-4a75-b04d-f08aac7bfab3
-- title:
--   Theorem 1.1 — no Borel bound modulo null sets at $\Delta^0_3$
-- statement:
--   There are one compact metrizable abelian group $K$, its normalized Haar probability $\lambda$, and one family of subgroups $(H_T)_{T\in\mathrm{WF}}$ with the following properties. Every $H_T$ is $\Delta^0_3$ in $K$. Every graph $\{(x,y):x^{-1}y\in H_T\}$ is $\Delta^0_3$ in $K^2$ and is a difference of two $F_\sigma$ sets. For every Borel equivalence relation $F$ on an arbitrary standard Borel space there is a well-founded tree $T$ such that
--
--   $$E_{H_T}^K\mathbin{\upharpoonright}C\not\leq_B F
--   \qquad\text{for every Borel }C\subseteq K\text{ with }\lambda(C)=1.$$
--
--   The compact group, measure, and whole family precede the arbitrary target. The selected tree may depend on $F$, but it must work against every Borel conull domain for that target. No invariance of $C$ is required. A reduction on $C$ would have to preserve and reflect the relations on every pair in $C^2$, not just almost every pair for the product measure. Empty target spaces are included; no countability of the full well-founded-tree index set is imposed.
-- source:
--   Universality modulo null sets in the Borel hierarchy, user-supplied unpublished manuscript dated 9 November 2026; SHA-256 48745c75427f83370292c2e4cf91ec06377e80472252db0182599edcd05e2d97, Theorem 1.1, lines 58–71; context lines 73–91 and the modulo-null convention in Section 2. The manuscript has no public URL supplied.

import Definitions.Def_ModNullCompact20261109

set_option autoImplicit false

theorem ModNullUniversality.theorem1_1 :
    ∃ K : ModNullUniversality.CompactMetrizableHaarGroup,
      ModNullUniversality.IsAbelian K ∧
      ∃ H : ModNullUniversality.WF → Subgroup K.Carrier,
        ModNullUniversality.LowComplexityFamily K H ∧
        ∀ F : ModNullUniversality.StandardBorelEquivalence,
          ∃ T : ModNullUniversality.WF,
            ∀ C : Set K.Carrier, MeasurableSet C → K.haar C = 1 →
              ¬ ModNullUniversality.BorelReducible
                (fun x y : C => ModNullUniversality.CosetRelation K (H T) x.val y.val)
                F.rel := by sorry
