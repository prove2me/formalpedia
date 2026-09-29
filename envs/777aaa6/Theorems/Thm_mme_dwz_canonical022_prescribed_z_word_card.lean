-- Prove2me | Theorems.Thm_mme_dwz_canonical022_prescribed_z_word_card
-- name    : mme_dwz_canonical022_prescribed_z_word_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T06:58:42.471021+00:00
-- url     : https://prove2.me/theorems/737d1ecd-0bd6-45c5-bc0e-b6bb0462e4c7
-- title:
--   Exact canonical 022 prescribed-Z word cardinality
-- statement:
--   For every natural CW parameter $q$, integer Z-split profile $p$ with positive denominator $d$ and equal outer counts $c_0=c_2$, and every $m\ge0$, put $N=dm$, $L=c_0m$, and $G=c_1m$. The number of retained actual canonical coarse-grade-two Z words is
--
--   $$\binom{N}{L}\binom{N-L}{L}\,q^{2G}.$$
--
--   Here the words use the canonical coarse-pair subset basis and the prescribed counts are measured by the actual left CW grade. The identity includes $q=0$, $m=0$, and empty retained sets. It is a finite coordinate-count identity, not an unrestricted tensor-value bound or entropy limit. Combined with the actual canonical022 prescribed-Z matrix-multiplication restriction, it supplies its closed dimension; equal outer counts remain an explicit hypothesis.
-- source:
--   Duan–Wu–Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5 (28 November 2023), https://arxiv.org/abs/2210.10173v5, Definition 3.9, Section 6.3 (printed p.59), and Section 7.3 following Lemma 7.14 (printed pp.71–72). The generic finite pattern count reuses the earlier square proof research/agents/dwz_table2_component_022_gap/Solution.lean, now connected by an actual canonical-word equivalence.

import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue

universe u

set_option autoImplicit false

theorem mme_dwz_canonical022_prescribed_z_word_card
    (q : ℕ) (p : IntegerZSplitProfile 3)
    (houter : p.count 0 = p.count 2) (m : ℕ) :
    Nat.card {w : PowIndex (LiftedCoarsePair.{u} q 2) (p.length m) //
      prescribedZWord LiftedCoarsePair.leftGrade p m w} =
      Nat.choose (p.length m) (p.count 0 * m) *
        Nat.choose (p.length m - p.count 0 * m) (p.count 0 * m) *
          q ^ (2 * (p.count 1 * m)) := by sorry
