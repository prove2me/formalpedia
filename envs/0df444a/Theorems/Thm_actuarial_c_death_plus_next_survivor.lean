-- Prove2me | Theorems.Thm_actuarial_c_death_plus_next_survivor
-- name    : actuarial_c_death_plus_next_survivor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-13T06:22:47.104755+00:00
-- url     : https://prove2.me/theorems/71b016e3-e829-4b72-93a2-bfac7b64758c
-- title:
--   Disjoint annual death and next-anniversary survival
-- statement:
--   For any nonnegative integer realised death-year index k and policy year j, the indicator of being alive at the beginning of year j equals the indicator of death in that year plus the indicator of remaining alive at the next anniversary. The two events are disjoint even at the censoring boundary; this is the event identity used in every finite annual decrement proof.
--
--   The original mathematical identity is an open formal mission target. Its type has been copied exactly from a successful private remote Lean proof, which does not establish acceptance of this individual Prove2Me target.
-- source:
--   Original actuarial formalisation informed by S. David Promislow (2015), Fundamentals of Actuarial Mathematics, third edition, Chapters 3 and 5. Where the result is pure finite-sum algebra, it is an independently derived supporting identity, not claimed as a verbatim textbook theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_c_alive
import Definitions.Def_actuarial_c_death

open ActuarialAssurances

theorem actuarial_c_death_plus_next_survivor (k j : ℕ) :
    alive k j = death k j + alive k (j+1) := by sorry
