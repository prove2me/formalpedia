-- Prove2me | Theorems.Thm_AnalyticCombinatorics_Ch1_Polya_Bracelets_card_binary_bracelets
-- name    : AnalyticCombinatorics.Ch1.Polya.Bracelets.card_binary_bracelets
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-10-24T23:53:19.551522+00:00
-- url     : https://prove2.me/theorems/6bf30fdc-a674-4335-afdb-697395e3ddfe
-- title:
--   Binary bracelets under the dihedral action
-- statement:
--   Let $n$ be a natural number with $n>0$. Consider all binary colorings of the positions $\mathbb Z/n\mathbb Z$, identified under the full dihedral group of order $2n$. Its specified left action on positions sends $x$ to $x-i$ for a rotation $r_i$ and to $i-x$ for a reflection $sr_i$; colorings carry the induced inverse-precomposition action. Let $B_n$ be the number of coloring orbits. Then, as an equality of natural numbers,
--
--   $$B_n(2n)=\sum_{k\in\mathbb Z/n\mathbb Z}2^{\gcd(n,\bar k)}+
--   \begin{cases}
--   n\,2^{(n+1)/2},&n\bmod2=1,\\
--   (n/2)\,2^{n/2+1}+(n/2)\,2^{n/2},&n\bmod2\ne1.
--   \end{cases}$$
--
--   Here $\bar k$ is the least nonnegative representative of $k$, and each quotient in the formula is natural-number division. This is the orbit-count formula with the factor $2n$ retained. Rotations and reflections identify colorings; exchanging the two color names is not an additional equivalence.
-- source:
--   https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/AnalyticCombinatorics/Ch1/Polya/Bracelets.lean#L542
--   Source code license: Apache-2.0; https://github.com/xiangyazi24/AnalyticCombinatorics/blob/f6f3f1cebdae245a61d9d71e6b47c69fbd096fe3/LICENSE

import Definitions.Def_AnalyticCombinatorics_Ch1_Polya_Bracelets
import Mathlib

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option maxSynthPendingDepth 3
/-!
# Binary bracelets

This file applies the Pólya enumeration theorem to binary colorings of `ZMod n`
under the dihedral action.  With Mathlib's multiplication convention for
`DihedralGroup`, the compatible left action is `r i : x ↦ x - i` and
`sr i : x ↦ i - x`.
-/

open AnalyticCombinatorics AnalyticCombinatorics.Ch1 AnalyticCombinatorics.Ch1.Polya AnalyticCombinatorics.Ch1.Polya.Bracelets

open scoped BigOperators

attribute [local instance] arrowAction

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.Polya.Bracelets.orbitRelDecidableRel

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.Polya.Bracelets.orbitQuotientFintype

attribute [local instance] _root_.AnalyticCombinatorics.Ch1.Polya.Bracelets.subtypeFintypeClassical

variable {n : ℕ}

variable {n : ℕ} [NeZero n]

variable {n : ℕ} [NeZero n]

variable {n : ℕ} [NeZero n]

theorem AnalyticCombinatorics.Ch1.Polya.Bracelets.card_binary_bracelets (n : ℕ) (hn : 0 < n) :
    letI : NeZero n := ⟨Nat.ne_of_gt hn⟩
    Fintype.card
        (MulAction.orbitRel.Quotient (DihedralGroup n) (ZMod n → Bool)) * (2 * n) =
      (∑ k : ZMod n, 2 ^ Nat.gcd n k.val) +
        if n % 2 = 1 then
          n * 2 ^ ((n + 1) / 2)
        else
          n / 2 * 2 ^ (n / 2 + 1) + n / 2 * 2 ^ (n / 2) := by sorry
