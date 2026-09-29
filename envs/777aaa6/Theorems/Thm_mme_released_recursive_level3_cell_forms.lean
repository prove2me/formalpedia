-- Prove2me | Theorems.Thm_mme_released_recursive_level3_cell_forms
-- name    : mme_released_recursive_level3_cell_forms
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-23T05:17:11.126223+00:00
-- url     : https://prove2.me/theorems/3e7078a7-c68e-4e14-9312-678cdc8c8b3e
-- title:
--   Level-3 recursive stage data: closed forms of the cell word distributions
-- statement:
--   Closed forms for the cell word distributions of the level-three recursive stage data.
--
--   In the published stage data, each level-three region splits into cells; a cell carries a grade
--   triple `(a0, a1, a2)` summing to four and a free weight parameter `s` (a numerator over the scale
--   `D = 10^12`). The nine mode-`i` word weights of that cell, `cellDist`, are the values
--   `childW a0 a1 a2 s i w0 w1` for the nine complete words `(w0, w1)`, listed in the order
--   `3 w0 + w1`.
--
--   Two statements are made.
--
--   First, the definition is restated: the cell word list of a region's cell is exactly the nine
--   `childW` values of that cell's grade triple and parameter.
--
--   Second, and this is the content, those nine values are computed in closed form for every one of the
--   forty-five pairs (grade triple, mode) — fifteen triples summing to four, three modes — with the
--   parameter `s` left symbolic, subject only to `2 s <= D`. Every one of the forty-five is one of
--   exactly three shapes:
--
--   * a point mass: all of the weight `D` on a single word (eighteen of the forty-five);
--   * an even two-point split: weight `D / 2` on each of two words (eighteen of the forty-five);
--   * the one-parameter family `(s, D - 2 s, s)` on the three words `(0,2)`, `(1,1)`, `(2,0)`
--     (nine of the forty-five), which occurs exactly when the mode's own grade is two and the triple
--     has a zero or a pair of ones elsewhere.
--
--   So the parameter enters the word distribution only through that last family, and only in the
--   level-two way: the cell layer of level three carries no new shapes beyond the point mass, the fair
--   coin, and the symmetric three-point family.
-- source:
--   Alman-Duan-Vassilevska Williams-Xu-Xu-Zhou, More Asymmetry Yields Faster Matrix Multiplication (https://arxiv.org/abs/2404.16349), sections 5-6, applied to the published exact seed of the released parameters. Finite data and its verification; no exponent claim.

import Mathlib
import Definitions.Def_mme_released_recursive_stage_data
import Definitions.Def_mme_recursive_yz_owned_filters
open BigOperators MME MME.RecursiveYZ MME.RecStage
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem mme_released_recursive_level3_cell_forms :
    (∀ (ρ : Fin 6) (i : Fin 3) (r : Fin 88)
        (c : RecursiveThinSplit.Split (2 * 2 ^ (2 - 1)) (parent3 ρ r)),
      cellDist ρ i r c =
        (List.range 9).map (fun idx ↦
          childW (c.val 0).val (c.val 1).val (c.val 2).val (cellRec ρ r c).2 i.val
            (idx / 3) (idx % 3))) ∧
    ∀ s : ℕ, 2 * s ≤ D →
      ((List.range 9).map (fun idx ↦ childW 0 0 4 s 0 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 0 4 s 1 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 0 4 s 2 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, 0, 0, 0, D]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 1 3 s 0 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 1 3 s 1 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 1 3 s 2 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, D / 2, 0, D / 2, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 2 2 s 0 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 2 2 s 1 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 2 2 s 2 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 3 1 s 0 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 3 1 s 1 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, D / 2, 0, D / 2, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 3 1 s 2 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 4 0 s 0 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 4 0 s 1 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, 0, 0, 0, D]) ∧
      ((List.range 9).map (fun idx ↦ childW 0 4 0 s 2 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 0 3 s 0 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 0 3 s 1 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 0 3 s 2 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, D / 2, 0, D / 2, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 1 2 s 0 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 1 2 s 1 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 1 2 s 2 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 2 1 s 0 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 2 1 s 1 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 2 1 s 2 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 3 0 s 0 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 3 0 s 1 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, D / 2, 0, D / 2, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 1 3 0 s 2 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 0 2 s 0 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 0 2 s 1 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 0 2 s 2 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 1 1 s 0 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 1 1 s 1 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 1 1 s 2 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 2 0 s 0 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 2 0 s 1 (idx / 3) (idx % 3)) =
        [0, 0, s, 0, D - 2 * s, 0, s, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 2 2 0 s 2 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 3 0 1 s 0 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, D / 2, 0, D / 2, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 3 0 1 s 1 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 3 0 1 s 2 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 3 1 0 s 0 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, D / 2, 0, D / 2, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 3 1 0 s 1 (idx / 3) (idx % 3)) =
        [0, D / 2, 0, D / 2, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 3 1 0 s 2 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 4 0 0 s 0 (idx / 3) (idx % 3)) =
        [0, 0, 0, 0, 0, 0, 0, 0, D]) ∧
      ((List.range 9).map (fun idx ↦ childW 4 0 0 s 1 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) ∧
      ((List.range 9).map (fun idx ↦ childW 4 0 0 s 2 (idx / 3) (idx % 3)) =
        [D, 0, 0, 0, 0, 0, 0, 0, 0]) := by sorry
