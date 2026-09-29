-- Prove2me | Theorems.Thm_mme_dwz_canonical022_prescribed_z_word_card_general
-- name    : mme_dwz_canonical022_prescribed_z_word_card_general
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T07:11:04.023494+00:00
-- url     : https://prove2.me/theorems/951f0fca-91c5-46bb-be06-0705c3fa3a4c
-- title:
--   Exact canonical 022 word count for arbitrary prescribed Z profiles
-- statement:
--   For every natural CW parameter $q$, integer Z-split profile $p$ with positive denominator $d$ and counts $c_0+c_1+c_2=d$, and every $m\ge0$, put $N=dm$, $A=c_0m$, $B=c_1m$, and $C=c_2m$. The number of retained actual canonical coarse-grade-two Z words is
--
--   $$\binom{N}{A}\binom{N-A}{C}\,q^{2B}.$$
--
--   The counts use the actual left CW grade in the canonical coarse-pair basis. The outer counts need not agree, so the theorem applies to the asymmetric rational candidate without changing its probabilities. It includes $q=0$, zero powers and empty retained sets. Combined with the actual prescribed-Z canonical022 matrix-multiplication restriction, this gives the literal finite source's closed scalar-product dimension. It does not assert an entropy limit or exponent bound.
-- source:
--   Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 (28 November 2023), https://arxiv.org/abs/2210.10173v5, Definition 3.9 and Section 7.3 after Lemma 7.14. Section 6.3 presents the symmetric special case. The general finite formula counts actual canonical Z letters: one grade-0 corner, q² grade-1 middle pairs, and one grade-2 corner. The proof generalizes the prior square multinomial argument, preserving the canonical word/profile equivalence.

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue

universe u

set_option autoImplicit false

theorem mme_dwz_canonical022_prescribed_z_word_card_general
    (q : ℕ) (p : IntegerZSplitProfile 3) (m : ℕ) :
    Nat.card {w : PowIndex (LiftedCoarsePair.{u} q 2) (p.length m) //
      prescribedZWord LiftedCoarsePair.leftGrade p m w} =
      Nat.choose (p.length m) (p.count 0 * m) *
        Nat.choose (p.length m - p.count 0 * m) (p.count 2 * m) *
          q ^ (2 * (p.count 1 * m)) := by sorry
