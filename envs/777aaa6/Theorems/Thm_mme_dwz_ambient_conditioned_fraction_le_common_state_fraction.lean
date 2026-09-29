-- Prove2me | Theorems.Thm_mme_dwz_ambient_conditioned_fraction_le_common_state_fraction
-- name    : mme_dwz_ambient_conditioned_fraction_le_common_state_fraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-28T03:25:25.718493+00:00
-- url     : https://prove2.me/theorems/2b113f91-9e43-48ad-8e94-ebc5d2bc7f8f
-- title:
--   Normalized ambient DWZ mass survives canonical family selection
-- statement:
--   Under the same canonical affine state and selected injective owner family, normalize both broken-copy nonhole cardinalities by their common useful-block cardinal. The ambient conditioned nonhole fraction is at most the selected common-state nonhole fraction:
--
--   $$
--   \frac{|\operatorname{nonholes}(B_{\mathrm{amb}})|}{|\operatorname{UsefulBlock}|}
--   \le
--   \frac{|\operatorname{nonholes}(B_{\mathrm{sel}})|}{|\operatorname{UsefulBlock}|}.
--   $$
--
--   This termwise inequality transfers the weighted ambient Claim 6.8 mass to the enumerated common-state copies without changing the quantitative constant.
-- source:
--   Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Additional Zeroing-Out Step 2 and Claim 6.8, printed pp. 51--55; https://arxiv.org/abs/2210.10173

import Definitions.Def_mme_dwz_global_common_state_broken_copy
import Definitions.Def_mme_dwz_global_ambient_conditioned_broken_copy
import Theorems.Thm_mme_dwz_table2_affine_hash_bucket_mem_iff_retains
import Theorems.Thm_mme_dwz_ambient_conditioned_nonholes_le_common_state_selected

open MME

set_option autoImplicit false

/-!
# Normalized ambient mass survives selected-family restriction

This is the exact termwise form needed after weighted enumeration.  Canonical
bucket membership supplies affine retention at the common state, the proved
cardinality transport compares nonholes, and division by the common useful-
block cardinal preserves the inequality.
-/

theorem mme_dwz_ambient_conditioned_fraction_le_common_state_fraction
    (m : ℕ) {p N L k : ℕ} [Fact p.Prime] (hpodd : Odd p)
    (reindex : Fin (N + 1) ≃ Fin L)
    (S : Finset ℕ) (hSrange : S ⊆ Finset.range (p / 2))
    (hSfree : ThreeAPFree (S : Set ℕ))
    (A : Finset (Fin (N + 1) → Fin 15))
    (Tnative : Finset (Fin L → Fin 15))
    (q : (Fin (N + 2) → ZMod p) × ZMod p)
    (edge : Fin k → Fin (N + 1) → Fin 15)
    (hedgeT : ∀ j,
      MME.DWZGlobalCorrelated.sourceWord reindex edge j ∈ Tnative)
    (hedgeInjective : Function.Injective edge)
    (r : Fin k)
    (hedgeBucket : edge r ∈ MME.dwzTable2AffineHashBucket S A q) :
    let retained := MME.DWZGlobalCorrelated.sourceWord reindex edge r
    (((MME.DWZGlobalCorrelated.ambientConditionedBrokenCopy
          m reindex Tnative retained (hedgeT r)
            (fun t ↦ q.1 t.castSucc)).nonholes.card : ℕ) : ℝ) /
        (Fintype.card
          (MME.DWZTable2StandardForm.UsefulBlock m retained) : ℝ) ≤
      MME.DWZSquare.nonholeFraction
        (MME.DWZGlobalCorrelated.commonStateBrokenCopy
          m reindex q edge r) := by
  sorry
