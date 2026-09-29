-- Prove2me | Theorems.Thm_mme_dwz_fourth_coupled63_exact_power_six_values
-- name    : mme_dwz_fourth_coupled63_exact_power_six_values
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-20T14:24:25.37915+00:00
-- url     : https://prove2.me/theorems/2db3456e-2496-4c10-9895-75d816d38f3d
-- title:
--   Exact three-mode power six-values for all sixty-three canonicalized q=5 coupled square rows
-- statement:
--   The $q=5$ fourth-power ledger contains sixty-three canonicalized coupled square rows. Row $i$ carries integer parameters $l_i, g_i$ with $341\,l_i < 100\,g_i$, a block shape $\rho_i$ which is one of the three orientations $(1,1,2)$, $(1,2,1)$, $(2,1,1)$, and a rational rate $r_i$.
--
--   For every field $K$ and every row $i$ there is a complete-split profile family $\beta$ such that the **exact** three-mode power of that row's canonical square block,
--
--   $$\mathrm{restrictedPower}_K\big(5, \rho_i, \beta, 0, N\big), \qquad N = 2\,(l_i + g_i)\,m ,$$
--
--   has six-symmetrized restriction rate at least $\exp(r_i)$ at $\tau = 790643/10^6$. Explicitly: for every base strictly below $\exp(r_i)$ and every cutoff there is a multiplicity $m$ beyond it with an actual finite direct sum of matrix-multiplication tensors restricting from the six-symmetrization of that exact power, carrying total $\tau$-weight at least the base raised to $6N$.
--
--   The tolerance is $\varepsilon = 0$: all three mode profiles are pinned exactly, not merely the Z histogram. This is the form required by a consumer that has decomposed a tensor into cells whose three mode profiles are all prescribed — for example the cells of a recursive block decomposition — where the accepted prescribed-Z endpoints of these same rows are not applicable, since a value for the larger prescribed-Z power does not bound the value of the smaller exact-profile subtensor.
--
--   The rate $r_i$ is the row's stored ledger rate; the theorem re-derives it from the row parameters through the same exact rational logarithm certificates used by the accepted prescribed-Z version, so no new numerical claim is introduced.
-- source:
--   Supporting lemma for the exact-profile (three-mode) child values of the Duan-Wu-Zhou fourth-power recursive construction; complete-profile analogue of the accepted prescribed-Z statements. See https://arxiv.org/html/2210.10173v5 and https://arxiv.org/html/2404.16349v2 . No asymptotic exponent claim.

import Definitions.Def_mme_dwz_fourth_coupled63_canonical_row_data

open MME Module MME.DWZRestrictedValue MME.Coupled63Scalar MME.CompleteSplit
universe u
set_option autoImplicit false

theorem mme_dwz_fourth_coupled63_exact_power_six_values (K : Type u) [Field K] (i : Fin 63) :
    ∃ beta : Fin 3 → CompleteSplit.Profile 2,
      HasSixSequenceRate TensorObj.Restrict
        (fun m ↦ CompleteSplitCanonicalSquare.restrictedPower K 5 (rho i) beta 0
          (2 * (((rows i).l + (rows i).g) * m)))
        (fun m ↦ (2 * (((rows i).l + (rows i).g) * m)))
        (790643 / 1000000 : ℝ) (Real.exp ((rows i).rate : ℝ)) := by sorry
