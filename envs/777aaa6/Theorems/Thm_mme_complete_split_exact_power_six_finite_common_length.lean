-- Prove2me | Theorems.Thm_mme_complete_split_exact_power_six_finite_common_length
-- name    : mme_complete_split_exact_power_six_finite_common_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T14:32:32.491839+00:00
-- url     : https://prove2.me/theorems/4afb0051-97e1-4494-a6ea-e3329307c2f3
-- title:
--   A common physical length for a finite family of exact complete-profile powers
-- statement:
--   Let $J$ be a finite index set and, for each $j$, let $T_j$ be a tensor with chosen bases, complete-word labels, a profile family $\beta_j$, and a unit length $\ell_j > 0$. Suppose each member has a six-symmetrized restriction rate at least $V_j$ along its own exact complete-profile sequence,
--
--   $$m \;\longmapsto\; T_j^{[\beta_j]}{}_{\ell_j m}, \qquad \text{length } \ell_j m ,$$
--
--   and fix bases $v_j$ with $0 < v_j < V_j$.
--
--   Then there is a single $L_0 > 0$ such that **every** member has an actual finite matrix witness at **every** common length $L_0 r$:
--
--   $$\ell_j \mid L_0 r \qquad\text{and}\qquad \bigoplus \langle a,b,c\rangle \;\trianglelefteq\; \mathrm{six}\big(T_j^{[\beta_j]}{}_{L_0 r}\big), \quad v_j^{\,6 L_0 r} \le \sum (abc)^{\tau} .$$
--
--   The sequence rates alone give each member witnesses only along its own cofinal set of multiplicities, which need not meet. Taking one witness length $N_j$ per member and setting $L_0 = \prod_j N_j$ makes every $N_j$ divide $L_0$, and the witness-power statement for exact complete-profile powers lifts each member's witness from $N_j$ to any multiple.
--
--   This is what a Kronecker product across the family needs: all factors must be taken at the same physical length. It is the complete-profile analogue of the accepted prescribed-Z common-length statement, and it is the form required when the members are cells of a block decomposition, whose three mode profiles are all pinned.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_mode_word_basis
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME MME.CompleteSplit MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open BigOperators
open scoped NNReal

universe u w

set_option autoImplicit false

theorem mme_complete_split_exact_power_six_finite_common_length
    {K : Type u} [Field K] {J : Type w} [Fintype J]
    (T : J → TensorObj K 3) {ι : J → Fin 3 → Type u} {ell : J → ℕ}
    (b : (j : J) → (i : Fin 3) → Basis (ι j i) K ((T j).V i))
    (label : (j : J) → (i : Fin 3) → ι j i → CompleteWord (ell j))
    (beta : (j : J) → Fin 3 → Profile (ell j))
    (len : J → ℕ) (hlen : ∀ j, 0 < len j)
    (tau : ℝ) (V v : J → ℝ)
    (hpos : ∀ j, 0 < v j) (hstrict : ∀ j, v j < V j)
    (hvalue : ∀ j, HasSixSequenceRate TensorObj.Restrict
      (fun m ↦ restrictedPower (T j) (b j) (label j) (beta j) 0 (len j * m))
      (fun m ↦ len j * m) tau (V j)) :
    ∃ L₀ : ℕ, 0 < L₀ ∧ ∀ (r : ℕ) (j : J),
      len j ∣ L₀ * r ∧
      SixFiniteWitness TensorObj.Restrict
        (restrictedPower (T j) (b j) (label j) (beta j) 0 (L₀ * r)) (L₀ * r) tau (v j) := by sorry
