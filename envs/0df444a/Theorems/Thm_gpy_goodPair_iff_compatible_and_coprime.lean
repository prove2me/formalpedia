-- Prove2me | Theorems.Thm_gpy_goodPair_iff_compatible_and_coprime
-- name    : gpy_goodPair_iff_compatible_and_coprime
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T01:08:47.106184+00:00
-- url     : https://prove2.me/theorems/9922a444-a307-49ab-9fbc-2738dcf1d932
-- title:
--   Characterization of good pairs
-- statement:
--   A support pair $(d,e)$ is good at a coordinate $i$ if and only if it is compatible and some witness $w$ of the joint divisibility system has $w + h_i$ coprime to the combined modulus $L$. The forward direction packages the compatibility of good pairs with the witness itself; the backward direction is the definition of goodness. Formalization Note: goodness and compatibility are both written out in Mathlib terms, with no local definitions.
-- source:
--   GPY first-moment comparison, formalized from Mathlib (compatible pairs, good pairs, and the singular sum)

import Mathlib
open Classical

theorem gpy_goodPair_iff_compatible_and_coprime {k : ℕ} {h d e : Fin k → ℕ}
    {i : Fin k} :
    (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) ↔
    (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))]) ∧
      ∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
        Nat.Coprime (w + h i)
          (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) := by sorry
