-- Prove2me | Theorems.Thm_mme_cwFourth_kronPow_word_basis_coefficients_symmetric
-- name    : mme_cwFourth_kronPow_word_basis_coefficients_symmetric
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T10:25:04.11232+00:00
-- url     : https://prove2.me/theorems/f50c70f2-d637-481d-8982-8c1e24cd924b
-- title:
--   Powers of CW_5^4 have mode-permutation-invariant coefficients
-- statement:
--   Let $T = CW_5^{\otimes 4} = (CW_5 \otimes CW_5) \otimes (CW_5 \otimes CW_5)$ be the Stothers fourth power of the Coppersmith–Winograd tensor with $q = 5$. Give each mode its canonical basis: the tensor product of the standard coordinate bases, indexed by coordinates $((a,b),(c,d)) \in \{0,\dots,6\}^4$. Give the Kronecker power $T^{\otimes n}$ the induced word basis in every mode, indexed by words $x_i : \{0,\dots,n-1\} \to \{0,\dots,6\}^4$.
--
--   **Statement.** For every $n$ and every permutation $\sigma$ of the three modes, the coefficients of $T^{\otimes n}$ in this basis are invariant under permuting the modes:
--   $$\big[T^{\otimes n}\big]_{(x_{\sigma(0)},\, x_{\sigma(1)},\, x_{\sigma(2)})} \;=\; \big[T^{\otimes n}\big]_{(x_0,\, x_1,\, x_2)} .$$
--
--   The coefficient of a word triple is the product over positions and over the four atomic factors of $CW_5$ coefficients. $CW_5$ is invariant under all mode permutations in its standard basis, so the product is too.
--
--   This is the basis-level symmetry hypothesis of `mme_basis_projected_mode_permutation_iso`. It lets an all-mode projection of $T^{\otimes n}$ be moved to any mode orientation.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite tensor statement; no asymptotic exponent claim.

import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_kronPow_position_permutation_linear_data

open MME MME.TensorObj MME.StothersFourth MME.CompleteSplit.CWFourth Module

universe u

set_option autoImplicit false

theorem mme_cwFourth_kronPow_word_basis_coefficients_symmetric (K : Type u) [Field K] (n : ℕ)
    (σ : Equiv.Perm (Fin 3)) (x : Fin 3 → Fin n → ULift.{u} (Coordinate 5)) :
    (Basis.piTensorProduct (fun i ↦ kronPowModeWordBasis (cwFourthObj K 5) i
        ((cwFourthCanonicalBasis K 5 i).reindex Equiv.ulift.symm) n)).repr
        ((cwFourthObj K 5).kronPow n).t (fun i ↦ x (σ i)) =
      (Basis.piTensorProduct (fun i ↦ kronPowModeWordBasis (cwFourthObj K 5) i
        ((cwFourthCanonicalBasis K 5 i).reindex Equiv.ulift.symm) n)).repr
        ((cwFourthObj K 5).kronPow n).t x := by sorry
