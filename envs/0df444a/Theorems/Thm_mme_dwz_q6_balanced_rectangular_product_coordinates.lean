-- Prove2me | Theorems.Thm_mme_dwz_q6_balanced_rectangular_product_coordinates
-- name    : mme_dwz_q6_balanced_rectangular_product_coordinates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T08:53:49.069919+00:00
-- url     : https://prove2.me/theorems/65796c6a-c727-4fd3-aba7-fd5cd1dd08a9
-- title:
--   Two six-channel fibers in the balanced q=6 rectangular alphabets
-- statement:
--   For the square of the Coppersmith--Winograd tensor at $q=6$, each canonical rectangular coarse-$Z$ alphabet of grade $3$ or grade $1$ consists of two fibers of six letters. There are explicit equivalences
--
--   $$
--   I_3\simeq[2]\times[6],\qquad I_1\simeq[2]\times[6].
--   $$
--
--   Under the grade-$3$ equivalence, fiber labels $0,1$ have canonical left split grades $2,1$ respectively. Under the grade-$1$ equivalence, they have left split grades $0,1$ respectively. This is the finite coordinate fact behind the equal-multiplicity counts for Table-2 rows $013$, $031$, $103$, and $301$.
-- source:
--   Duan--Wu--Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section 6.3 and Table 2, rectangular components 013, 031, 103, and 301.

import Definitions.Def_mme_dwz_component_word_projection
import Mathlib.Tactic

open MME
open MME.DWZComponentRestriction

universe u

set_option autoImplicit false

theorem mme_dwz_q6_balanced_rectangular_product_coordinates :
    (∃ e3 : MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6 3 ≃
        Fin 2 × Fin 6,
      ∀ p, p.leftGrade = ![2, 1] (e3 p).1) ∧
    (∃ e1 : MME.DWZComponentRestriction.LiftedCoarsePair.{u} 6 1 ≃
        Fin 2 × Fin 6,
      ∀ p, p.leftGrade = ![0, 1] (e1 p).1) := by
  sorry
