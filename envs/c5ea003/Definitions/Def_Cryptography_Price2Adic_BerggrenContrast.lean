-- Prove2me | Definitions.Def_Cryptography_Price2Adic_BerggrenContrast
-- name    : Cryptography_Price2Adic_BerggrenContrast
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:22:01.397678+00:00
-- url     : https://prove2.me/theorems/1b67b87b-ed75-4d36-ac09-9a0bb62e48ae
-- title:
--   Aether Catalog definitions — Cryptography_Price2Adic_BerggrenContrast
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.Price2Adic.BerggrenContrast`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/Price2Adic/BerggrenContrast.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Cryptography_BerggrenTrees_BerggrenFreeMonoid

/-!
# Contrast: the Berggren alphabet is 2-adically invisible

`Letters.lean` proved that the *Price* alphabet is read, two letters deep, by the residue
`N mod 8` of the odd leg.  Here we prove the complementary negative statement for the
*Berggren* tree, whose generators are the ones already formalised in
`Cryptography.BerggrenTrees.BerggrenFreeMonoid` (`actGen`):

  `A : (m,n) ↦ (2m-n, m)`,  `B : (m,n) ↦ (2m+n, m)`,  `C : (m,n) ↦ (m+2n, n)`.

* `berg_children_diff` — the `A`- and `B`-children of a node have triples differing by
  `8mn`, `4mn`, `8mn`; so they are congruent modulo `4mn`.
* `berg_twoAdic_blind` — for every `k` there is a primitive node whose `A`- and
  `B`-children are distinct primitive triples that agree modulo `2^k` in all three
  entries.  Hence **no** function of the 2-adic residues of a triple can recover the last
  Berggren letter, at any depth of the 2-adic filtration.

Together with `Price2Adic.letter_pos0_iff` (`A` iff `N ≡ 1 mod 4`, a perfect classifier)
this makes the placement precise: the two trees are sealed at different adic places, and
the halving alphabet of Price is exactly the one that the 2-adic filtration can read.

## Lab notes (round 70, exp 548)

The reported best Berggren-letter `z`-score at modulus `2^j` (worst `z = +4.57`) failed
replication under three fresh seeds; the theorem below shows why any such signal must be
a sampling artefact: the separating statistic does not exist.
-/

namespace Price2Adic

/-- Euclid's triple map on integer parameter pairs. -/
def tripleZ (p : ℤ × ℤ) : ℤ × ℤ × ℤ := (p.1 ^ 2 - p.2 ^ 2, 2 * p.1 * p.2, p.1 ^ 2 + p.2 ^ 2)

/-- Primitive Euclid parameter pairs, over `ℤ` (the coefficient ring of `actGen`). -/
def ValidZ (p : ℤ × ℤ) : Prop :=
  0 < p.2 ∧ p.2 < p.1 ∧ IsCoprime p.1 p.2 ∧ (p.1 + p.2) % 2 = 1




end Price2Adic


