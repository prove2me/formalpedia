-- Prove2me | solution 2 for Catalog.Novelty.PellSpine.pellP_injective
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-17T19:32:30.408619+00:00
-- url     : https://prove2.me/submissions/44410dc4-4156-49a1-97b9-8fc08e65c04b

import Mathlib
import Definitions.Def_Novelty_PellSpineCore

open Catalog.Novelty.PellSpine

private lemma pellP_lt_succ : ∀ n, pellP n < pellP (n + 1)
  | 0 => by simp [pellP]
  | 1 => by simp [pellP]
  | n + 2 => by
      have h1 : pellP (n + 1) < pellP (n + 2) := pellP_lt_succ (n + 1)
      have h0 : pellP n < pellP (n + 1) := pellP_lt_succ n
      change 2 * pellP (n + 1) + pellP n < 2 * pellP (n + 2) + pellP (n + 1)
      -- equivalent to pellP (n+1) + pellP n < 2 * pellP (n+2) after rearranging,
      -- but omega handles the inequalities from h0,h1
      omega

theorem solution : Function.Injective pellP :=
  StrictMono.injective (strictMono_nat_of_lt_succ pellP_lt_succ)
