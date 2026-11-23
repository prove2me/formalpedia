-- Prove2me | Theorems.Thm_exists_mem_kaplanskySet_eq_of_le
-- name    : exists_mem_kaplanskySet_eq_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T08:13:20.581208+00:00
-- url     : https://prove2.me/theorems/02c77754-653b-4466-a659-a7ba1219e9c9
-- title:
--   exists mem kaplansky Set eq of le: exists mem kaplansky Set eq of le
-- statement:
--   If `0 ∉ S`, then there is a maximal element in `kaplanskySet S`.
--
--   Source: https://github.com/riccardobrasca/kaplanski4/blob/0989e6dc65081ab46709aac8a204a65f58ff52ee/Kaplanski4/Kaplanski.lean#L33-L36
-- source:
--   https://github.com/riccardobrasca/kaplanski4/blob/0989e6dc65081ab46709aac8a204a65f58ff52ee/Kaplanski4/Kaplanski.lean#L33-L36

import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
import Mathlib.RingTheory.UniqueFactorizationDomain.Ideal
import Mathlib.RingTheory.PowerSeries.Ideal
import Definitions.Def_Kaplanski4_Kaplanski
set_option autoImplicit false
variable {R : Type*}
open Set Ideal Submonoid
variable [Semiring R] {S : Subsemigroup R} {P : Ideal R}

theorem exists_mem_kaplanskySet_eq_of_le (hS : 0 ∉ S) :
    ∃ P ∈ kaplanskySet S, ∀ I ∈ kaplanskySet S, P ≤ I → I = P := by sorry
