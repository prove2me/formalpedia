-- Prove2me | Theorems.Thm_c5_three_port_pairing
-- name    : c5_three_port_pairing
-- status  : Proved
-- author  : @hao jia
-- created : 2026-09-25T21:10:11.657688+00:00
-- url     : https://prove2.me/theorems/263ac12b-987a-42da-a98a-2a03f52f91d0
-- title:
--   A three-port pairing lemma for the 5-cycle
-- statement:
--   Let C₅ be the cycle on five vertices, indexed by Fin 5, with adjacency between consecutive indices modulo 5. Choose distinct nonadjacent vertices u and v, and let T be the other three vertices. For any reserved vertex r in T, the other four vertices can be covered by two disjoint edges of C₅ such that each edge has exactly one endpoint in T.
--
--   This is a finite local pairing lemma only; it makes no claim about extending the pairing to a larger graph or proving a global P₃-factor. No novelty claim is asserted.
-- source:
--   Original finite local derivation; no external source or novelty claim is asserted.

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic

theorem c5_three_port_pairing :
    ∀ (u v r : Fin 5),
      u ≠ v →
      ¬ ((u.val + 1) % 5 = v.val ∨ (v.val + 1) % 5 = u.val) →
      let T : Finset (Fin 5) := (Finset.univ.erase u).erase v
      r ∈ T →
      ∃ (a b c d : Fin 5),
        a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        ((a.val + 1) % 5 = b.val ∨ (b.val + 1) % 5 = a.val) ∧
        ((c.val + 1) % 5 = d.val ∨ (d.val + 1) % 5 = c.val) ∧
        ({a, b, c, d} : Finset (Fin 5)) = Finset.univ.erase r ∧
        ((a ∈ T ∧ b ∉ T) ∨ (a ∉ T ∧ b ∈ T)) ∧
        ((c ∈ T ∧ d ∉ T) ∨ (c ∉ T ∧ d ∈ T)) := by sorry
