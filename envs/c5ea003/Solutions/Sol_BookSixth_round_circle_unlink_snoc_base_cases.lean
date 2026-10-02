-- Prove2me | solution 1 for BookSixth.round_circle_unlink_snoc_base_cases
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T02:35:33.200536+00:00
-- url     : https://prove2.me/submissions/a916960c-be92-45a8-b1aa-eb60d54d03da

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_single_round_circle_motion_to_standard
open scoped BigOperators
open BookSixth

noncomputable section

-- The `n = 0` and `n = 1` cases of
-- `BookSixth.round_circle_unlink_snoc` (`6181fc76`).
--
-- * `n = 0`: `Fin.snoc (fun _ : Fin 0 => ∅) E` is the single circle `E`, and
--   moving it to `standardCircle 0` is the `Proved` theorem
--   `BookSixth.single_round_circle_motion_to_standard` (`9c911921`). The
--   hypothesis `hpairs` is not needed, which is what makes this case
--   non-circular.
-- * `n = 1`: `Fin.snoc (Fin.cons D Fin.elim0) E` is `![D, E]`, whose `IsUnlink`
--   is exactly the hypothesis `hpairs`.
--
-- Note the appended circle must be *independent* of the family. Taking the
-- appended circle to be `D` itself would make the goal `IsUnlink ![D, D]`,
-- i.e. one homeomorphism sending `D` to two disjoint standard circles, which
-- is false.
--
-- The two rewriting steps below are proved by `fin_cases` on the index
-- followed by `rfl`. For `n = 0` the domain `Fin 1` has the single value
-- `Fin.last 0`, which is not of the form `j.castSucc` for any `j : Fin 0`, so
-- `Fin.snoc` returns the appended circle `E`. For `n = 1` the domain `Fin 2`
-- has the value `Fin.last 1`, giving `E`, and the value `(0 : Fin 1).castSucc`,
-- giving `Fin.cons D Fin.elim0 0 = D`. Hence `![D, E]`.
--
-- The index computation is discharged with Mathlib's own `Fin.snoc_zero`,
-- `Fin.snoc_last` and `Fin.snoc_castSucc` (all in `Mathlib/Data/Fin/Tuple/Basic`),
-- rather than by unfolding `Fin.snoc` and letting `simp` generate a `Fin.induction`
-- side goal. `Fin.snoc_zero` is the exact `rfl` lemma for the `n = 0` case, so
-- `hn0` needs no case analysis at all.

theorem solution (D E : Set Space3)
    (hroundD : RoundCircle D) (hroundE : RoundCircle E)
    (hpairs : IsUnlink (![D, E] : Fin 2 → Set Space3)) :
    IsUnlink (Fin.snoc (fun _ : Fin 0 => (∅ : Set Space3)) E) ∧
    IsUnlink (Fin.snoc (Fin.cons D Fin.elim0) E) := by
  have hn0 : Fin.snoc (fun _ : Fin 0 => (∅ : Set Space3)) E
      = (fun _ : Fin 1 => E) := by
    exact Fin.snoc_zero _ E
  have hn1 : Fin.snoc (Fin.cons D Fin.elim0) E
      = (![D, E] : Fin 2 → Set Space3) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact Fin.snoc_last _ _
    · rw [Fin.snoc_castSucc]
      fin_cases j <;> rfl
  rw [hn0, hn1]
  refine ⟨?_, hpairs⟩
  obtain ⟨K, hKf, hKi, hK0, hKend, _⟩ :=
    BookSixth.single_round_circle_motion_to_standard E hroundE
  refine ⟨K, hKf, hKi, hK0, ?_⟩
  intro i
  simpa using hKend

end
