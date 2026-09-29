-- Prove2me | Theorems.Thm_mme_Ctensor_three_unequal_all_words_min_pair_extraction
-- name    : mme_Ctensor_three_unequal_all_words_min_pair_extraction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T00:38:36.453536+00:00
-- url     : https://prove2.me/theorems/4484ce8d-ba81-492a-b6a1-92067f3d16a4
-- title:
--   All words yield unequal three-star extractions at the minimum pair-power rate
-- statement:
--   Let $X,Y,Z$ have actual C-tensor certificates with positive component counts $H_0,H_1,H_2$ and constant matrix-multiplication component volumes $v_0,v_1,v_2$. For every integer $R\ge0$, there are $k$ matrix-multiplication tensors with dimensions $a_i,b_i,c_i$ satisfying
--   $
--   \bigoplus_{i=1}^k\langle a_i,b_i,c_i\rangle
--   \le_{\mathrm{restriction}}
--   \bigl(X\otimes\operatorname{cyc}(Y)\otimes\operatorname{cyc}^2(Z)\bigr)^{\otimes R},
--   \qquad
--   a_ib_ic_i=(v_0v_1v_2)^R,
--   $
--   and
--   $
--   k\ge\frac{\min((H_0H_1)^R,(H_0H_2)^R,(H_1H_2)^R)}{2}
--   \exp\!\left(-100\sqrt{\log\bigl(\min(H_0^R,H_1^R,H_2^R)+1\bigr)}\right).
--   $
--
--   The result allows independent alphabets and component volumes. It needs no balanced word frequencies, divisibility, or common component dimensions, and includes $R=0$. This supplies an actual finite extraction with a quantitative count, not a scalar value assumption or a new exponent bound.
-- source:
--   Derived finite composition of Prove2Me mme_Ctensor_three_unequal_word_induced_matching_extraction (published targetfe76e44b-437d-45ef-9340-a26122a99793) with the Proved rectangular support theorem mme_rectangular_MM_support_min_pair_matching (ac5ca90b-1b65-4c65-b589-7bd380765458). The underlying cyclic C-tensor grading/extraction construction was previously verified as mme_Ctensor_three_cyclic_balanced_grading_certificate (70dd3098-5d4f-4668-88bf-a3ddbd48c6a1) and mme_Ctensor_three_balanced_cyclic_induced_matching_extraction (92df093a-e7af-4448-b1b5-497ac31a6896). This finite all-word specialization is an explicitly derived adapter rather than a separately numbered theorem in a paper. The balanced-frequency assumptions of the older exported interfaces are unnecessary when only the common matrix-product volume, rather than equality of all three component dimensions, is required.

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_threeStarCyclicProduct
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MME

universe u

set_option autoImplicit false

theorem mme_Ctensor_three_unequal_all_words_min_pair_extraction
    {K : Type u} [Field K] {X Y Z : TensorObj K 3}
    {H0 H1 H2 v0 v1 v2 : ℕ}
    (certX : CTensorOneHOneCertificate X H0 v0)
    (certY : CTensorOneHOneCertificate Y H1 v1)
    (certZ : CTensorOneHOneCertificate Z H2 v2)
    (h0 : 0 < H0) (h1 : 0 < H1) (h2 : 0 < H2) (R : ℕ) :
    ∃ (k : ℕ) (a b c : Fin k → ℕ),
      TensorObj.Restrict
        (TensorObj.bigAdd (fun i ↦ MMObj K (a i) (b i) (c i)))
        ((threeStarCyclicProduct X Y Z).kronPow R) ∧
      (((min ((H0 * H1) ^ R)
          (min ((H0 * H2) ^ R) ((H1 * H2) ^ R)) : ℕ) : ℝ) / 2) *
        Real.exp (-100 * Real.sqrt
          (Real.log (((min (H0 ^ R) (min (H1 ^ R) (H2 ^ R)) + 1 : ℕ) : ℝ)))) ≤
        (k : ℝ) ∧
      (∀ i, a i * b i * c i = (v0 * v1 * v2) ^ R) := by sorry
