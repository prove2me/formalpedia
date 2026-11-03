-- Prove2me | Theorems.Thm_FSCofinality_theorem1_2
-- name    : FSCofinality.theorem1_2
-- status  : Proved
-- author  : @username
-- created : 2026-11-02T12:41:46.367698+00:00
-- url     : https://prove2.me/theorems/b774fd72-07d9-402c-a4df-1a2a2c2f9242
-- title:
--   Theorem 1.2 — Friedman--Stanley cofinality without Borel completeness
-- statement:
--   There are one fixed countable relational language L and one isomorphism-invariant Borel class K of L-structures on the natural numbers such that every countable level of the concrete product-limit Friedman--Stanley hierarchy Borel reduces to isomorphism on K, while graph isomorphism does not. Moreover, bounded-rank well-founded rooted tree isomorphism reduces to the same target for every nonzero countable bound, including finite and empty tree codes. Borelness is a property of K as a class of structures, not a requirement that its isomorphism graph be Borel. The language and target class are fixed before the ordinal quantifiers, while each ordinal may have its own reduction. The product-limit and original-tree presentations make the cofinality convention explicit.
--
--   The same $L$ and $\mathcal K$ satisfy $$\forall\alpha<\omega_1,\quad\mathsf J_\alpha\leq_B\cong_{\mathcal K},\qquad \cong_{\mathrm{Graph}}\not\leq_B\cong_{\mathcal K},$$ together with $$\forall\,0<\alpha<\omega_1,\quad\cong_{\mathfrak T_\alpha}\leq_B\cong_{\mathcal K}.$$ Here $\mathfrak T_\alpha$ uses the explicitly defined global reverse-tree-height presentation; ordinal indices are not identified with those of a different rank convention.
-- source:
--   Friedman--Stanley cofinality and Borel completeness: A proposed negative answer to the Friedman--Stanley question, supplied research draft dated 2 November 2026, FriedmanStanleyQuestion.tex, Theorem 1.2, label thm:main, lines 130--143; assembly lines 1745--1763; hierarchy conventions in Section 2.3 and Propositions 4.13, 4.15.

import Definitions.Def_FSCofinalityHierarchy20261102
import Definitions.Def_FSCofinalityTrees20261102

set_option autoImplicit false

theorem FSCofinality.theorem1_2 :
    ∃ L : FSCofinality.CountableRelationalLanguage,
      ∃ K : Set (FSCofinality.Structures L),
        MeasurableSet K ∧ FSCofinality.IsInvariant K ∧
        (∀ a : Ordinal.{0}, a < Ordinal.omega 1 →
          (FSCofinality.fsTower a).Reduces (FSCofinality.classRelation L K)) ∧
        ¬ FSCofinality.graphRelation.Reduces (FSCofinality.classRelation L K) ∧
        (∀ a : Ordinal.{0}, 0 < a → a < Ordinal.omega 1 →
          (FSCofinality.RootedTrees.treeRelation a).Reduces
            (FSCofinality.classRelation L K)) := by sorry
