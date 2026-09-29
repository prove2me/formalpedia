-- Prove2me | Theorems.Thm_mme_prescribed_graded_alphabet_word_card
-- name    : mme_prescribed_graded_alphabet_word_card
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-21T18:40:20.965789+00:00
-- url     : https://prove2.me/theorems/392151b6-0144-448d-9577-bc54e8738587
-- title:
--   Exact prescribed-profile word count for a nonuniform graded alphabet
-- statement:
--   For any finite graded alphabet, the number of words with a prescribed rational grade profile equals the multinomial coefficient times the product of grade-fiber cardinalities raised to their prescribed counts.
-- source:
--   Exact type-class enumeration for the prescribed Z-word restrictions used in Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, Definitions 3.7 and 8.1.

import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Mathlib.Data.Nat.Choose.Multinomial
open MME MME.DWZComponentRestriction MME.DWZRestrictedValue
open scoped BigOperators
universe u
set_option autoImplicit false

theorem mme_prescribed_graded_alphabet_word_card
    {I : Type u} [Fintype I] [DecidableEq I] {t : ℕ}
    (grade : I → Fin t) (p : IntegerZSplitProfile t) (m : ℕ) :
    Nat.card {w : PowIndex I (p.length m) // prescribedZWord grade p m w} =
      Nat.multinomial Finset.univ (fun a ↦ p.count a * m) *
        ∏ a, (Fintype.card {i : I // grade i = a}) ^ (p.count a * m)  := by sorry
