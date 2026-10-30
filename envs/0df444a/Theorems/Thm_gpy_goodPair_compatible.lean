-- Prove2me | Theorems.Thm_gpy_goodPair_compatible
-- name    : gpy_goodPair_compatible
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-30T01:08:43.427236+00:00
-- url     : https://prove2.me/theorems/0832a982-49a3-4143-b8b3-d85b82d16fc8
-- title:
--   Every good pair is compatible
-- statement:
--   A support pair $(d,e)$ is good at a coordinate $i$ when some witness $w$ satisfies the joint divisibility system and $w + h_i$ is coprime to the combined modulus $L$. Such a pair is always compatible: the compatibility congruences are just differences of two divisibilities of the witness, reduced modulo the gcd of the two coordinate moduli. This holds unconditionally, for any tuple and any pair. Formalization Note: goodness and compatibility are both written out in Mathlib terms, with no local definitions.
-- source:
--   GPY first-moment comparison, formalized from Mathlib (compatible pairs, good pairs, and the singular sum)

import Mathlib
open Classical

theorem gpy_goodPair_compatible {k : ℕ} {h d e : Fin k → ℕ} {i : Fin k}
    (hg : ∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i)
        (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) :
    ∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
      h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))] := by sorry
