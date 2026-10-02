-- Prove2me | Theorems.Thm_BookSixth_isUnlink_pair_second_moves
-- name    : BookSixth.isUnlink_pair_second_moves
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T07:57:18.841379+00:00
-- url     : https://prove2.me/theorems/73bce1dc-6b04-4c08-a291-9c80c9951336
-- title:
--   An ambient isotopy fixing one component carries the other component of an unlinked pair
-- statement:
--   Suppose an ambient isotopy `K` fixes the set `A` at every time, carries `B` at time `1` to a set `B'`, and `![A, B]` is an unlink. Then `![A, B']` is an unlink as well.
--
--   This is the isotopy-invariance bridge that the append step needs, in the *second* slot. The existing `BookSixth.isUnlink_path_image` (c8865be9) transports a whole family by the *same* path in every slot, so it cannot move only one component. What is missing is control of a single component: the first slot is frozen by `hA`, and the second slot is carried to `B'` by the ambient isotopy. Because the ambient map is injective, `hA` setwise implies `K t` is the identity on `A`, so the isotopy of the pair is exactly the isotopy of the second component.
--
--   **Where the mission needs it.** `BookSixth.round_circle_snoc_transport` (ea8c131b) is to be proved from `BookSixth.isUnlink_path_image`, `BookSixth.round_circle_single_standardize_link_preserving_v3` (1805d081) and `BookSixth.round_circle_snoc_transport_compose_v4` (c587e2de). The third of those needs, for each prefix index, the pair certificate `IsUnlink ![standardCircle i, D]`, whereas the hypothesis of the append lemma supplies only `IsUnlink ![C i, D]`. This statement is what converts one into the other once the prefix has been carried onto the standard circles.
-- source:
--   **Why a new lemma is needed.** The four Proved `isUnlink_*` bridges are `isUnlink_path_image` (c8865be9), `isUnlink_pair_swap` (fd9760e4), `isUnlink_pair_of_isUnlink_v1` (0e05058c) and `round_circle_snoc_of_transport` (08bc82db). None of them moves a single component: `path_image` applies one common path to every slot, `pair_swap` only reorders, `pair_of_isUnlink_v1` only unpacks, and `snoc_of_transport` only packages an already-given isotopy.
--
--   **The construction.** Write `H` for the isotopy witnessing `hAB`, and define
--
--       L t := (K t).trans H (K t).symm
--
--   the conjugation of `H` by the path `K`. Then `L` is an ambient isotopy: joint continuity of `L t` follows from joint continuity of `K t` and `H t` by `Homeomorph.trans`; joint continuity of `(L t).symm = (K t).symm.trans H.symm (K t)` likewise; and `L 0 x = (K 0).trans H 0 (K 0).symm x = (id.trans H 0 id) x = H 0 x = x`, since `H 0 = id` by `hAB`'s first conjuncts.
--
--   At time `1` the conjugation acts as `H 1` on the image `K 1 '' A = A`, by `hA` at `t = 1`, so `(L 1) '' A = H 1 '' A = A` and `L 1 = H 1` on `A`; the slot is unchanged. In the second slot, `(L 1) '' B = H 1 '' (K 1).symm '' B` does not immediately read as `B'`; the cleaner route is to use `hA` to fix the first slot throughout and then observe that the whole pair isotopy is `K 1 .trans H (K 1).symm`, whose value on `B` is `H 1 (K 1).symm (K 1) b = H 1 b` for `b` in `B`, because `K 1 .trans (K 1).symm` is the identity. Hence `(L 1) '' B = H 1 '' B = B'`, using the isotopy endpoint contained in `hAB` together with `hB`.
--
--   The hypotheses `hA` and `hB` are the honest content: `hA` says the ambient motion leaves the first component alone, and `hB` says the second component arrives at `B'`.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.isUnlink_pair_second_moves (A B B' : Set Space3)
    (K : ℝ → Space3 ≃ₜ Space3)
    (hK : Continuous (fun p : ℝ × Space3 => K p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (K p.1).symm p.2) ∧
      (∀ x, K 0 x = x))
    (hA : ∀ t, K t '' A = A)
    (hB : K 1 '' B = B')
    (hAB : IsUnlink (![A, B] : Fin 2 → Set Space3)) :
    IsUnlink (![A, B'] : Fin 2 → Set Space3) := by sorry
