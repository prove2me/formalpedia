-- Prove2me | Theorems.Thm_mme_dwz_table2_equation22_outer_layout_compatibility_rate
-- name    : mme_dwz_table2_equation22_outer_layout_compatibility_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T15:17:53.749901+00:00
-- url     : https://prove2.me/theorems/9cdb45c5-bb85-40a2-9d3b-e17196c3716f
-- title:
--   Regional layouts imply the full Table-2 Equation-(22) compatibility rate
-- statement:
--   Fix a positive multiplier $m$, a finite nonempty family $\mathcal O$ of outer
--   objects, a finite position set $P$, and a coarse word
--   $K:P\to\{0,\ldots,4\}$.  Let $R_m$ be the canonical disjoint union of the
--   nine boundary and five interior Table-2 regions, and write $d(x)$ for the
--   coarse $Z$-degree of the region containing $x\in R_m$.  Suppose every
--   $I\in\mathcal O$ supplies an equivalence
--
--   $$
--   L_I:R_m\simeq P
--   \qquad\text{with}\qquad
--   K(L_I(x))=d(x)\quad\text{for all }x\in R_m.
--   $$
--
--   Then there is an assembly map $\Phi$ from an outer object together with a
--   complete Table-2 regional split assignment to a typical fine word above $K$.
--   For each fixed $I$, the map $A\mapsto\Phi(I,A)$ is injective.  Moreover, some
--   typical word $b$ satisfies the full division-free Equation-(22) bound
--
--   $$
--   |\mathcal O|\,\exp\!\bigl(mS\log(2)L_P\bigr)
--   \;\le\;
--   P(m)\,
--   \bigl|\{I\in\mathcal O:\exists A,\ \Phi(I,A)=b\}\bigr|,
--   $$
--
--   where $S=10^{16}$, $L_P$ is the exact Table-2 compatibility exponent, and
--   $P(m)$ is the explicit fixed-degree polynomial loss in the formal statement.
--   The theorem does not assume the $A_km$ histogram of $K$, an assembly map, or
--   fixed-outer injectivity; all three are derived from the layout family.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Definition 6.4, Lemma 6.7, and Equations (22)--(23), printed pp. 54--56 (PDF pp. 55--57), specialized to the exact q=6 data in Section 6.3 and Table 2, printed p. 59 (PDF p. 60); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_equation22_outer_layout_compatibility_rate
    (m : ℕ) (hm : 0 < m)
    {Outer Position : Type*}
    [Finite Outer] [Nonempty Outer]
    [Fintype Position]
    (K : Position → Fin 5)
    (layout : ∀ _I : Outer,
      (Σ r : MME.DWZTable2Cardinality.SplitRegion,
        MME.DWZTable2Cardinality.RegionPosition m r) ≃ Position)
    (hlayout : ∀ (I : Outer) x,
      K (layout I x) = MME.DWZTable2Cardinality.coarseDegree x.1) :
    let BtypicalK :=
      {small : Position → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} =
          MME.DWZTable2Counts.gamma p * m}
    ∃ assemble :
        (Σ _I : Outer, MME.DWZTable2Cardinality.SplitAssignments m) →
          BtypicalK,
      (∀ I, Function.Injective (fun A ↦ assemble ⟨I, A⟩)) ∧
      ∃ small : BtypicalK,
        (Nat.card Outer : ℝ) *
            Real.exp
              ((m : ℝ) * (MME.DWZTable2Counts.scale : ℝ) * Real.log 2 *
                MME.DWZSquare.logAlphaP) ≤
          ((6 * ((MME.DWZTable2Counts.scale * m + 1 : ℕ) : ℝ)) ^ 5 *
            (∏ s : Fin 15,
              if MME.DWZSquare.shapeX s = 0 ∨
                  MME.DWZSquare.shapeY s = 0 then
                (6 *
                  ((MME.DWZTable2Counts.component s * m + 1 : ℕ) : ℝ)) ^ 3
              else 1) *
            (∏ k : Fin 5,
              (6 *
                ((MME.DWZTable2Counts.plusMass k * m + 1 : ℕ) : ℝ)) ^ 3)) *
            (Nat.card
              {I : Outer //
                ∃ A : MME.DWZTable2Cardinality.SplitAssignments m,
                  assemble ⟨I, A⟩ = small} : ℝ) := by
  sorry
