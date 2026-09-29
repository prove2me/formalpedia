-- Prove2me | solution 1 for mme_stothers_phi116_fourth_tensor_term_expansion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:23:18.722907+00:00
-- url     : https://prove2.me/submissions/87460224-4e61-4a29-9fd6-29c06707335f

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi116_term_expansion
import Definitions.Def_mme_CW_fourth_literal_support_words
import Theorems.Thm_mme_CW_fourth_tensor_eq_sum_literal_terms

open MME TensorProduct Module BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

namespace MME.StothersFourth.Phi116

private theorem cwTermTriple_eq_literal
    (q : ℕ) (t : CWTerm q) (s : Fin 3) :
    cwTermTriple q t s =
      MME.StothersFourth.cwLiteralTermTriple q t s := by
  rcases t with ⟨i, r⟩ | r <;> fin_cases r <;> fin_cases s <;> rfl

private theorem cwTermMonom_eq_literal
    (K : Type u) [Field K] (q : ℕ) (t : CWTerm q) :
    cwTermMonom K q t =
      MME.StothersFourth.cwLiteralTermMonomial K q t := by
  unfold cwTermMonom MME.StothersFourth.cwLiteralTermMonomial
  rw [cwTermTriple_eq_literal, cwTermTriple_eq_literal,
    cwTermTriple_eq_literal]

end MME.StothersFourth.Phi116

theorem solution
    (K : Type u) [Field K] :
    (MME.StothersFourth.cwFourthObj K 6).t =
      ∑ t₄ : MME.StothersFourth.Phi116.CWTerm 6,
      ∑ t₃ : MME.StothersFourth.Phi116.CWTerm 6,
      ∑ t₂ : MME.StothersFourth.Phi116.CWTerm 6,
      ∑ t₁ : MME.StothersFourth.Phi116.CWTerm 6,
        interchange
          (interchange
            (MME.StothersFourth.Phi116.cwTermMonom K 6 t₁)
            (MME.StothersFourth.Phi116.cwTermMonom K 6 t₂))
          (interchange
            (MME.StothersFourth.Phi116.cwTermMonom K 6 t₃)
            (MME.StothersFourth.Phi116.cwTermMonom K 6 t₄)) := by
  simpa only [MME.StothersFourth.Phi116.cwTermMonom_eq_literal] using
    mme_CW_fourth_tensor_eq_sum_literal_terms K 6
