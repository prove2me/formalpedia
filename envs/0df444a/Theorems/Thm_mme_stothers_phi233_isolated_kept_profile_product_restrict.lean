-- Prove2me | Theorems.Thm_mme_stothers_phi233_isolated_kept_profile_product_restrict
-- name    : mme_stothers_phi233_isolated_kept_profile_product_restrict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:07:05.834691+00:00
-- url     : https://prove2.me/theorems/a915c899-a342-4ae9-b35f-4b4e2f79998b
-- title:
--   Each isolated retained $\Phi_{233}$ edge carries the exact cyclic profile product
-- statement:
--   Fix a field $K$, a Coppersmith--Winograd parameter $q$, and an exact $\Phi_{233}$ profile with multiplicities $\alpha,\beta,\gamma,\delta$ over words of length $2N$. Suppose a retained set $S$ of cyclic exact-profile edges is isolated inside the same-marginal completion family, and no two retained edges share a vertex in any of the three modes. Let $P$ denote the ten-factor tensor product prescribed by that profile. Then
--
--   $$
--   \bigoplus_{e\in S} \operatorname{cyc}(P)\;\leq_{\mathrm{res}}\;\operatorname{cyc}(T_{233})^{\otimes 2N}.
--   $$
--
--   Thus every retained combinatorial edge contributes one identical cyclic profile tensor to the degeneration. This is the direct algebraic interface between the asymmetric-hashing extraction and the value lower bound in the Davie--Stothers laser analysis.
--
--   **Formalization Note** The isolation hypothesis is expressed against the full same-marginal ambient family, while membership in the exact target family supplies the exact joint profile for each retained edge.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 5.1(v) and the extraction argument on pp. 365--367; https://www.maths.ed.ac.uk/~sandy/a11164.pdf

import Definitions.Def_mme_stothers_phi233_cyclic_finsets
import Definitions.Def_mme_stothers_phi233_outer_grading
import Definitions.Def_mme_CW_2376_address_block
import Theorems.Thm_mme_bigAdd_mono_restrict
import Theorems.Thm_mme_stothers_phi233_isolated_kept_blocks_restrict
import Theorems.Thm_mme_stothers_phi233_exact_cyclic_component_product_restrict_address_block

open MME

universe u

set_option autoImplicit false

theorem mme_stothers_phi233_isolated_kept_profile_product_restrict
    {K : Type u} [Field K] (q : ℕ)
    {N alpha beta gamma delta : ℕ}
    (kept : Finset
      (MME.StothersFourth.Phi233.CyclicAmbientEdge
        N alpha beta gamma delta))
    (hkept : kept ⊆
      MME.StothersFourth.Phi233.targetFinset
        N alpha beta gamma delta)
    (hisolated :
      ∀ e ∈ MME.StothersFourth.Phi233.ambientFinset
          N alpha beta gamma delta,
        (∀ i : Fin 3, ∃ f ∈ kept,
          MME.StothersFourth.Phi233.cyclicModeWord e i =
            MME.StothersFourth.Phi233.cyclicModeWord f i) →
        e ∈ kept)
    (hmode : ∀ i : Fin 3,
      Function.Injective (fun e : kept ↦
        MME.StothersFourth.Phi233.cyclicModeWord e.1 i)) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin kept.card ↦
        cyclicSymmetrization
          (TensorObj.kronFin 10 (fun r ↦
            (MME.StothersFourth.Phi233.componentObj K q r).kronPow
              (MME.StothersFourth.Phi233.profileMultiplicity
                alpha beta gamma delta r)))))
      ((cyclicSymmetrization
        (MME.StothersFourth.cwFourthConstituent K q 2 3 3)).kronPow
          (2 * N)) := by
  sorry
