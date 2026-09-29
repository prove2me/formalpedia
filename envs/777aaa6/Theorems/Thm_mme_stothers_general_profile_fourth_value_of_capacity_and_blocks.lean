-- Prove2me | Theorems.Thm_mme_stothers_general_profile_fourth_value_of_capacity_and_blocks
-- name    : mme_stothers_general_profile_fourth_value_of_capacity_and_blocks
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-08T06:04:59.126172+00:00
-- url     : https://prove2.me/theorems/c7f3f6bb-4e3f-471d-b151-c9ce8eda4623
-- title:
--   Fourth-power value from capacity and block values
-- statement:
--   **Capacity plus block values give the fourth-power $\tau$-value, at any profile and any rate.**
--
--   Fix a strictly positive integral ten-class profile $\beta$, an exponent $\tau$, and a target rate
--   $G$. Suppose
--
--   - **(support)** every nonzero block of the canonical nine-grading of $CW_6^{\otimes4}$ has grade sum
--     $8$;
--   - **(capacity)** for some $C\ge0$ and all large $m$ there is an induced, mode-disjoint family $F$ of
--     exact-profile addresses of length $N = 3Dm$ with
--     $$G^{N}e^{-C\sqrt{N+1}} \;\le\; |F| \cdot \prod_{i=1}^{10} v_i(\tau)^{\,n_i\beta_i m};$$
--   - **(blocks)** every exact-profile address block has $\tau$-value at least any $W\ge0$ strictly below
--     that same inner product $\prod_i v_i(\tau)^{n_i\beta_i m}$.
--
--   Then $CW_6^{\otimes4}$ has $\tau$-value at least every $V$ with $0\le V<G$.
--
--   This is the assembly step of the outer laser, and it is where the two halves meet: the capacity
--   hypothesis is the outer hash-and-Stirling estimate, the block hypothesis is the inner extraction
--   from Lemma 5.1 after cyclic regrouping, and everything between them -- induced-word zeroing so that
--   mixed address blocks vanish, direct-sum additivity of $\tau$-values over the surviving blocks,
--   transport through the restriction, and taking the $N$-th root -- is carried out here.
--
--   The rate $G$ is left free rather than fixed to $\mathrm{globalRate}(6,\tau,a,a)$, so the same node
--   serves the diagonal case and the general case where $G$ carries the Equation (3.4) combination loss
--   $\mathcal E(b)/\mathcal E(a)$.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3, Lemma 3.3 and Equations (3.2)-(3.4), and Section 5, Theorem 5.3; https://www.maths.ed.ac.uk/~sandy/a11164.pdf.

import Definitions.Def_mme_stothers_general_outer_profile
import Definitions.Def_mme_induced_word_zeroing
import Mathlib.Analysis.SpecialFunctions.Exp

open MME BigOperators Filter

universe u

set_option autoImplicit false

theorem mme_stothers_general_profile_fourth_value_of_capacity_and_blocks
    {K : Type u} [Field K]
    (base : Fin 10 → ℕ) (hbase : ∀ r, 0 < base r)
    (tau : ℝ) (G : ℝ)
    (hblockSupport : ∀ sigma : Fin 3 → Fin 9,
      (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma ≠ 0 →
        (∑ s, ((sigma s).val : ℕ)) = 8)
    (hcapacity : ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in Filter.atTop,
        ∃ F : Finset (MME.StothersFourth.GenExactOuterAddress base m),
          MME.StothersFourth.GenInducedModeDisjoint F ∧
          G ^ (MME.StothersFourth.genOuterLength base m) *
              Real.exp
                (-C * Real.sqrt
                  (((MME.StothersFourth.genOuterLength base m + 1 : ℕ) : ℝ))) ≤
            (F.card : ℝ) *
              (∏ r : Fin 10,
                (MME.StothersFourth.classValue 6 tau r) ^
                  (MME.StothersFourth.classMultiplicity r *
                    MME.StothersFourth.genProfileCount base m r)))
    (hblocks : ∀ (m : ℕ)
        (a : MME.StothersFourth.GenExactOuterAddress base m) (W : ℝ),
      0 ≤ W →
      W < (∏ r : Fin 10,
        (MME.StothersFourth.classValue 6 tau r) ^
          (MME.StothersFourth.classMultiplicity r *
            MME.StothersFourth.genProfileCount base m r)) →
      HasTauValueAtLeast
        (gradedAddressBlock
          (MME.StothersFourth.cwFourthCanonicalGrading K 6) a.1)
        tau W) :
    ∀ V : ℝ, 0 ≤ V →
      V < G →
      HasTauValueAtLeast (MME.StothersFourth.cwFourthObj K 6) tau V := by
  sorry
