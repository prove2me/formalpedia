-- Prove2me | Theorems.Thm_mme_prescribed_cell_sampling_collision_bound
-- name    : mme_prescribed_cell_sampling_collision_bound
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-13T16:30:15.547359+00:00
-- url     : https://prove2.me/theorems/d853b57c-dab3-4b25-ad6c-a12b18372d17
-- title:
--   Finite repeated-sample bound for arbitrary cells
-- statement:
--   If every queried cell has at least m positions, the number of sample tuples with a repetition times m is at most the square of the query count times the total number of sample tuples. Proved by an injection for each unequal index pair and a finite union bound.
-- source:
--   Quantitative finite realization for a jointly processed constituent region, connected to the physical recursive Y/Z extraction for More Asymmetry Yields Faster Matrix Multiplication, https://arxiv.org/html/2404.16349v2#S6 . This is a supporting lemma, not a proof of the regional asymptotic theorem or a numerical omega certificate.

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

open BigOperators
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

theorem mme_prescribed_cell_sampling_collision_bound {P C J : Type*} [Fintype P] [Fintype J]
    (cell : P → C) (q : J → P) (m : ℕ)
    (hm : ∀ j, m ≤ Fintype.card {p : P // cell p = cell (q j)}) :
    let Samples := (j : J) → {p : P // cell p = cell (q j)}
    m * Fintype.card {s : Samples // ¬ Function.Injective (fun j ↦ (s j).val)} ≤
      Fintype.card J ^ 2 * Fintype.card Samples := by sorry
