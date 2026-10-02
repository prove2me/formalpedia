-- Prove2me | Theorems.Thm_BookSixth_isUnlink_snoc_of_standardized_prefix
-- name    : BookSixth.isUnlink_snoc_of_standardized_prefix
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-28T08:36:10.394694+00:00
-- url     : https://prove2.me/theorems/a7256e95-2218-454a-b022-5ee538e4ced1
-- title:
--   Appending a circle to a prefix that is already carried to the standard circles by one isotopy
-- statement:
--   The composition step of the append lemma `BookSixth.round_circle_unlink_snoc` (`6181fc76`), isolated as a reusable theorem.
--
--   Suppose an ambient isotopy `P` already carries each component `C i` of a prefix to the corresponding standard circle `standardCircle i`, and a second ambient isotopy `G` carries the transported image `P 1 '' D` of a further circle to `standardCircle n` while fixing every `standardCircle i` setwise at every time. Then the single isotopy `fun t => (G t).trans (P t)` carries the appended family `Fin.snoc C D` to the standard circles in order, so `Fin.snoc C D` is an unlink.
--
--   This is exactly the composition that the `Proved` theorem `BookSixth.round_circle_snoc_transport_compose_v3` (`301c14de`) performs, repackaged with `IsUnlink (Fin.snoc C D)` as the conclusion so that it composes directly with the `IsUnlink`-valued append and induction steps. Nothing here is geometric: no roundness, disjointness or linking argument is used, only `Set.image_image` and the continuity algebra for `Homeomorph.trans`.
--
--   **Why the mission needs it.** `BookSixth.round_circle_unlink` (`2468ff3e`) is proved by induction on the number of components with `BookSixth.round_circle_unlink_snoc` (`6181fc76`) as the append step, and `6181fc76` is currently `Open`. Once this composition lemma is `Proved`, the combinatorial content of the append step is discharged and the only remaining obligation in `6181fc76` is producing a prefix isotopy `P` that carries the prefix to the standard circles *while keeping the transported image of `D` round* — that is `BookSixth.round_circle_prefix_standardize_preserves_appended_roundness` (`067c6497`).
-- source:
--   The composition `H t := (G t).trans (P t)` is the standard concatenation of two
--   ambient isotopies: `Homeomorph.trans_apply` makes it `fun x => G t (P t x)`, so
--   `(H 1) '' S = (G 1) '' ((P 1) '' S)` by `Set.image_image`. Continuity is the
--   accepted `compose_v3` (`301c14de`) algebra, copied verbatim: compose the forward
--   family of `G` with `p |-> (p.1, P p.1 p.2)` and the inverse family of `P` with
--   `p |-> (p.1, G p.1 p.2 p.2)`, then `simpa [H, Function.comp_def]`.
--
--   The conclusion splits by `Fin.lastCases` on the index `j : Fin (n+1)`. At `last n`,
--   `Fin.snoc_last` rewrites the component to `D` and the goal is
--   `(G 1) '' (P 1) '' D = standardCircle n`, which is `hGnew` after `Set.image_image`.
--   At `i.castSucc`, `Fin.snoc_castSucc` rewrites the component to `C i` and the goal
--   is `(G 1) '' ((P 1) '' C i) = standardCircle i.val`, closed by `hPold i` followed by
--   `hGpres 1 i`. The `hGpres` binder is written `(t : ℝ) (i : ℕ)` explicitly, because an
--   un-annotated `i` cannot be resolved: `Fin.val` is the projection it would need, and
--   inference has no `Fin` type to attach it to. No geometric content is used.

import Mathlib
import Definitions.Def_BookSixth
open scoped BigOperators
open BookSixth

theorem BookSixth.isUnlink_snoc_of_standardized_prefix {n : ℕ}
    (C : Fin n → Set Space3) (D : Set Space3)
    (P : ℝ → Space3 ≃ₜ Space3) (G : ℝ → Space3 ≃ₜ Space3)
    (hP : Continuous (fun p : ℝ × Space3 => P p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (P p.1).symm p.2) ∧
      (∀ x, P 0 x = x))
    (hG : Continuous (fun p : ℝ × Space3 => G p.1 p.2) ∧
      Continuous (fun p : ℝ × Space3 => (G p.1).symm p.2) ∧
      (∀ x, G 0 x = x))
    (hPold : ∀ i, (P 1) '' C i = standardCircle i.val)
    (hGnew : (G 1) '' (P 1) '' D = standardCircle n)
    (hGpres : ∀ (t : ℝ) (i : ℕ), (G t) '' standardCircle i = standardCircle i) :
    IsUnlink (Fin.snoc C D) := by sorry
