-- Prove2me | Theorems.Thm_mme_dwz_table2_equation22_distinct_outer_compatibility_rate
-- name    : mme_dwz_table2_equation22_distinct_outer_compatibility_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T15:00:34.549065+00:00
-- url     : https://prove2.me/theorems/32d0935e-c8fc-4979-a474-b591b1327428
-- title:
--   Table-2 Equation-(22) averaging counts distinct compatible outer blocks
-- statement:
--   Fix a positive repetition multiplier $m$, a finite family $\mathcal O$, and
--   a finite set of positions carrying a coarse Table-2 word $K$.  The fiber of
--   each coarse symbol $k\in\{0,\ldots,4\}$ is required to have size $A_km$,
--   where $A_k$ is the exact integral Table-2 $Z$-marginal.  Let
--   $\mathcal B_{\mathrm{typ},K}$ be the fine pair-words which coarsen pointwise
--   to $K$ and in which the pair $(r_\ell,r_r)\in\{0,1,2\}^2$ occurs exactly
--   $\Gamma_{r_\ell,r_r}m$ times.
--
--   Let $\mathcal A_m$ be the exact regional split-assignment space from
--   Equation (23).  Suppose there is an assembly map
--
--   $$
--   \Phi:\mathcal O\times\mathcal A_m\longrightarrow
--   \mathcal B_{\mathrm{typ},K}
--   $$
--
--   such that $A\mapsto\Phi(I,A)$ is injective for every fixed outer object
--   $I$.  Then some $b\in\mathcal B_{\mathrm{typ},K}$ satisfies
--
--   $$
--   |\mathcal O|\,
--   \exp\!\bigl(mS\log(2)\,L_P\bigr)
--   \;\le\;
--   P(m)\,
--   \bigl|\{I\in\mathcal O:\exists A\in\mathcal A_m,
--   \ \Phi(I,A)=b\}\bigr|.
--   $$
--
--   Here $S=10^{16}$, $L_P$ is the exact Table-2 compatibility exponent, and
--   $P(m)$ is the explicit product of the global, boundary-component, and five
--   interior fixed-degree polynomial losses displayed in the formal statement.
--
--   The theorem derives the exact cardinality and positivity of
--   $\mathcal B_{\mathrm{typ},K}$ internally, substitutes the exact
--   Equation-(23) numerator cardinality, and performs the Equation-(22)
--   averaging without natural-number division.  In particular, the right-hand
--   side counts distinct compatible outer objects, not assignment incidences.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Definition 6.4, Lemma 6.7, and Equations (22)--(23), printed pp. 54--56 (PDF pp. 55--57), specialized to the exact q=6 data in Section 6.3 and Table 2, printed p. 59 (PDF p. 60); https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_table2_split_assignments
import Theorems.Thm_mme_dwz_table2_equation23_numerator_count
import Theorems.Thm_mme_dwz_table2_compatibility_rate_division_free
import Theorems.Thm_mme_dwz_lemma6_7_typical_denominator_count
import Theorems.Thm_mme_dwz_table2_gamma_pushforward

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_equation22_distinct_outer_compatibility_rate
    (m : ℕ) (hm : 0 < m)
    {Outer Position : Type*}
    [Finite Outer] [Fintype Position] [DecidableEq Position]
    (K : Position → Fin 5)
    (hK : ∀ k,
      Fintype.card {t : Position // K t = k} =
        MME.DWZTable2Counts.alphaZ k * m) :
    let BtypicalK :=
      {small : Position → Fin 3 × Fin 3 //
        (∀ t, MME.DWZTable2Counts.coarseOf (small t) = K t) ∧
        ∀ p, Fintype.card {t : Position // small t = p} =
          MME.DWZTable2Counts.gamma p * m}
    ∀ (assemble :
        (Σ _I : Outer, MME.DWZTable2Cardinality.SplitAssignments m) →
          BtypicalK),
      (∀ I, Function.Injective (fun A => assemble ⟨I, A⟩)) →
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
