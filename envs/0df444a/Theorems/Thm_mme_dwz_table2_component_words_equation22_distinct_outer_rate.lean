-- Prove2me | Theorems.Thm_mme_dwz_table2_component_words_equation22_distinct_outer_rate
-- name    : mme_dwz_table2_component_words_equation22_distinct_outer_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-25T18:26:53.675724+00:00
-- url     : https://prove2.me/theorems/050d432e-5708-427b-b8ad-018c0f3ef3e1
-- title:
--   DWZ Equation (22): Table-2 component words give the compatibility rate
-- statement:
--   Fix a positive multiplier $m$, a finite nonempty family of outer objects, and a common coarse $Z$-word $K$. Suppose each outer object carries a fifteen-valued Table-2 component word, every component $s$ occurs exactly $m\,c_s$ times, and the $Z$-coordinate of the selected component agrees with $K$ at every position. Then there is an assembly map from each outer object and each legal local split assignment to a literal typical fine word above $K$, injective in the split assignment for every fixed outer object. Moreover, some typical fine word satisfies
--
--   $$
--   |\mathrm{Outer}|\,\exp\!\left(m\,10^{16}\log 2\,\log\alpha_P\right)
--   \le L(m)\,\#\{I:\exists A,\;\operatorname{assemble}(I,A)=\widehat K\},
--   $$
--
--   where $L(m)$ is the explicit polynomial factor displayed in the formal statement. This is the finite, division-free Equation-(22) averaging bound specialized to the exact joint component counts of Table 2. It removes all abstract regional-layout, coarse-histogram, assembly, and injectivity hypotheses from the source-facing interface.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173, Section 6.2, Definition 6.6, Equation (22), Lemma 6.7 and Equation (23) (printed pp. 54-56, PDF pp. 55-57), specialized to Section 6.3, Table 2 (printed pp. 58-59); https://arxiv.org/abs/2210.10173.

import Definitions.Def_mme_dwz_table2_split_assignments
import Definitions.Def_mme_dwz_table2_pair_coarsening

open scoped BigOperators

set_option autoImplicit false

theorem mme_dwz_table2_component_words_equation22_distinct_outer_rate
    (m : ℕ) (hm : 0 < m)
    {Outer Position : Type*}
    [Finite Outer] [Nonempty Outer]
    [Fintype Position]
    (K : Position → Fin 5)
    (shapeWord : Outer → Position → Fin 15)
    (hshape : ∀ (I : Outer) (s : Fin 15),
      Fintype.card {t : Position // shapeWord I t = s} =
        MME.DWZTable2Counts.component s * m)
    (hmatch : ∀ (I : Outer) (t : Position),
      MME.DWZSquare.shapeZ (shapeWord I t) = K t) :
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
                  assemble ⟨I, A⟩ = small} : ℝ) := by sorry
