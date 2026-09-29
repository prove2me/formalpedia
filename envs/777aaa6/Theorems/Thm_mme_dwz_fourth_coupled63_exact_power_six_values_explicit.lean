-- Prove2me | Theorems.Thm_mme_dwz_fourth_coupled63_exact_power_six_values_explicit
-- name    : mme_dwz_fourth_coupled63_exact_power_six_values_explicit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-21T10:40:14.583583+00:00
-- url     : https://prove2.me/theorems/c7f4a145-929a-4e8b-a1f3-6974cfb52a40
-- title:
--   Coupled63 exact-power six values with explicit orientation and profiles
-- statement:
--   This is the 63 canonicalized coupled rows of the $q=5$ fourth-power ledger, stated on their exact three-mode powers with every profile made explicit.
--
--   For each row $i$, with parameters $(l_i, g_i)$ and rate $r_i$, there is an orientation $e \in \{1, c, c^2\}$ ($c$ the cyclic mode permutation). The row's coarse square block is $\rho_i = (1,1,2)\circ e^{-1}$. There is also a complete-split profile triple $\beta$, whose mode-$m$ word probabilities are the canonical $(1,1,2)$ profiles read in orientation $e^{-1}(m)$:
--   $$\beta_m(\sigma) = \mathrm{profileProbability}\Big(\tfrac{l_i}{2(l_i+g_i)},\ e^{-1}(m),\ \sigma\Big).$$
--   In the $Z$-type mode this is $(p, 1-2p, p)$ on the words $02, 11, 20$. In the other two modes it is uniform on $01, 10$. For this $\beta$, the exact-profile powers of the canonical square block $\rho_i$ have six-symmetrized value $e^{r_i}$ at $\tau = 790643/10^6$:
--   $$\mathrm{HasSixSequenceRate}\Big(m \mapsto \mathrm{restrictedPower}\big(T_{\rho_i}, \beta, 0, 2(l_i+g_i)m\big),\ \tau,\ e^{r_i}\Big).$$
--
--   This strengthens `mme_dwz_fourth_coupled63_exact_power_six_values`, which only asserts that some $\beta$ exists. The explicit $\beta$ is needed to match the three-mode cell pieces of a More-Asymmetry regional extraction (`mme_canonical_square_piece_restricts_restrictedPower`) to these values.
-- source:
--   Duan-Wu-Zhou fourth-power recursive construction (https://arxiv.org/html/2210.10173v5, section 7) combined with the More-Asymmetry regional extraction (https://arxiv.org/html/2404.16349v2, section 6). Exact finite or asymptotic-rate statement as written; no exponent claim.

import Definitions.Def_mme_dwz_fourth_coupled63_canonical_row_data
import Definitions.Def_mme_complete_split_112_address_words

open MME Module MME.DWZRestrictedValue MME.Coupled63Scalar MME.CompleteSplit
universe u
set_option autoImplicit false

theorem mme_dwz_fourth_coupled63_exact_power_six_values_explicit (K : Type u) [Field K] (i : Fin 63) :
    ∃ e : Equiv.Perm (Fin 3), (e = 1 ∨ e = cyclicPerm ∨ e = cyclicPerm.trans cyclicPerm) ∧
      rho i = (fun a ↦ cwSquareBlockType 1 1 2 (e.symm a)) ∧
      ∃ beta : Fin 3 → CompleteSplit.Profile 2,
        (∀ mode sigma, (beta mode).probability sigma =
          (MME.CompleteSplit112.profileProbability
            (((rows i).l : ℚ) / (2 * (((rows i).l + (rows i).g : ℕ) : ℚ))) (e.symm mode)
              sigma : ℝ)) ∧
        HasSixSequenceRate TensorObj.Restrict
          (fun m ↦ CompleteSplitCanonicalSquare.restrictedPower K 5 (rho i) beta 0
            (2 * (((rows i).l + (rows i).g) * m)))
          (fun m ↦ (2 * (((rows i).l + (rows i).g) * m)))
          (790643 / 1000000 : ℝ) (Real.exp ((rows i).rate : ℝ)) := by sorry
