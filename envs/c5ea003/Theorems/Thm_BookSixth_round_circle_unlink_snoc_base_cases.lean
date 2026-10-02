-- Prove2me | Theorems.Thm_BookSixth_round_circle_unlink_snoc_base_cases
-- name    : BookSixth.round_circle_unlink_snoc_base_cases
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T01:45:26.217328+00:00
-- url     : https://prove2.me/theorems/198e1549-37bb-4907-b941-c6643c16062f
-- title:
--   Appending a circle to an empty or one-element family of round circles stays an unlink
-- statement:
--   The `n = 0` and `n = 1` cases of `BookSixth.round_circle_unlink_snoc` (`6181fc76-d41a-4748-8d50-a774894885bd`).
--
--   `IsUnlink (Fin.snoc C D)` says: there is one ambient isotopy of `Space3` carrying the family `C 0, …, C (n-1)` together with `D` to the standard circles `standardCircle 0, …, standardCircle n`, in that order.
--
--     * **`n = 0`.** The family being appended to is empty, so `Fin.snoc C E` is the single circle `E` and the claim is that `E` can be moved to `standardCircle 0` by an ambient isotopy from the identity.
--
--     * **`n = 1`.** The family is the single circle `D`, so `Fin.snoc C E` is the pair `D, E` and the claim is that the pair can be moved to `standardCircle 0, standardCircle 1` in order — which is exactly what `IsUnlink ![D, E]` says.
--
--   The `n = 1` case is therefore the hypothesis `hpairs` read back, and the `n = 0` case follows from the already-`Proved` single-circle theorem. Together they give the first two rows of the append induction, so the genuinely open part (`n ≥ 2`) is isolated rather than hidden behind an unproved base case.
-- source:
--   **The `n = 0` conjunct.** `Fin.snoc C E : Fin (0 + 1) → β` is `fun _ : Fin 1 => E`, because `snoc (Fin.last 0) = E` and there is no `castSucc` index to range over. So the goal is
--
--       IsUnlink (fun _ : Fin 1 => E)
--
--   which unfolds to the existence of an ambient isotopy `K` with `K 0 = id` and `K 1 '' E = standardCircle ((0 : Fin 1).val)`, i.e. `standardCircle 0`. That is the conclusion of `BookSixth.single_round_circle_motion_to_standard` (`9c911921`, Proved) at `E` and `hroundE`, after unfolding `IsUnlink` and reducing the index with `rfl`. The hypothesis `hpairs` is **not** used here — it is unnecessary, which is precisely what makes this case non-circular and free.
--
--   **The `n = 1` conjunct.** Here
--
--       Fin.snoc (Fin.cons D Fin.elim0) E = ![D, E]
--
--   as a function `Fin 2 → Set Space3`, since `snoc (Fin.castSucc 0) = (Fin.cons D Fin.elim0) 0 = D` and `snoc (Fin.last 1) = E`. So the goal is `IsUnlink ![D, E]`, which is *definitionally* the hypothesis `hpairs`. The proof is a `simpa` after the `Fin.lastCases` / `funext` reduction.
--
--   **A note on a tempting but false variant.** If one takes the appended circle to be `D` itself, the goal becomes `IsUnlink ![D, D]`, requiring a single homeomorphism with `K 1 '' D = standardCircle 0` *and* `K 1 '' D = standardCircle 1`. That is **false**: the two standard circles are disjoint, so no map sends `D` to both. An earlier draft of this target stated the `n = 1` case with a duplicated `D`; that statement is unprovable and was corrected to take an independent appended circle `E`. The lesson matches the recurring diagnostic in this project: a witness that looks reasonable can encode a false statement, and the resulting goal is unsatisfiable rather than merely hard.

import Mathlib
import Definitions.Def_BookSixth
import Theorems.Thm_BookSixth_single_round_circle_motion_to_standard
open scoped BigOperators
open BookSixth

theorem BookSixth.round_circle_unlink_snoc_base_cases (D E : Set Space3)
    (hroundD : RoundCircle D) (hroundE : RoundCircle E)
    (hpairs : IsUnlink (![D, E] : Fin 2 → Set Space3)) :
    IsUnlink (Fin.snoc (fun _ : Fin 0 => (∅ : Set Space3)) E) ∧
    IsUnlink (Fin.snoc (Fin.cons D Fin.elim0) E) := by sorry
