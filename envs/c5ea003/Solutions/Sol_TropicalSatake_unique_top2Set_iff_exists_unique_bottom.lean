-- Prove2me | solution 1 for TropicalSatake.unique_top2Set_iff_exists_unique_bottom
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T07:07:32.524608+00:00
-- url     : https://prove2.me/submissions/6f00fa20-2461-4e75-8766-4bad3a7492b7

-- Sol generated from Bridges/TropicalSatakeTop2Margin.lean
import Mathlib
import Definitions.Def_Bridges_TropicalSatakeTop2Margin
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Tropical Satake Top-2 Margin Theorem for GL₃ Hecke Score Classifiers

This file formalizes a sharp robustness theorem for top-2 label sets determined by
score triples `x : Fin 3 → ℝ`. The key results are:

1. **Unique top-2 set characterization**: A unique top-2 set exists iff there is a unique
   "bottom" class strictly below the other two.

2. **Perturbation stability**: If the minimum gap from the excluded class to the top-2 set
   exceeds `2ε`, then any coordinatewise `ε`-perturbation preserves the top-2 set.

3. **Sharp converse**: If one member of the top-2 set has margin at most `2ε` over the
   excluded class, then there exists an `ε`-perturbation destroying the top-2 set.

4. **Max-plus transfer**: For max-plus linear score models (tropical Satake reconstructions),
   test-family perturbation of size `η` induces score perturbation of size at most `η`,
   giving a concrete robustness certificate.

## Mathematical context

For GL₃ tropical Satake classifiers, scores are computed as max-plus linear forms on
a finite test family. The top-2 label set identifies the two most plausible classes.
Robustness of this label set under perturbation of the test valuations is the key
certification property. The sharp threshold is governed by the gap between the second
and third ordered scores—equivalently, the minimum separation between the excluded
class and the top-2 pair.
-/

open Finset

open TropicalSatake

/-! ## Core definitions -/



/-! ## Finite enumeration helpers for Fin 3 -/


/-
Any two-element subset of `Fin 3` has a unique complement element.
-/
lemma card_two_compl_singleton (A : Finset (Fin 3)) (hA : A.card = 2) :
    ∃! c : Fin 3, c ∉ A := by
  fin_cases A <;> simp_all +decide;
  · simp +decide [ ExistsUnique ];
  · simp +decide [ ExistsUnique ];
  · simp +decide [ ExistsUnique ]

/-! ## Section 1: Unique top-2 set characterization -/

/-
A unique top-2 set exists iff there is a unique bottom class strictly below
all others. This is the cleanest characterization for `Fin 3`.
-/

/-
Equivalent formulation: a unique top-2 set exists iff there is a class `c`
with positive margin to all other classes.
-/

/-! ## Section 2: Top-2 stability under coordinatewise perturbation -/

/-
Key inequality lemma: if `2ε < x a - x c` and both coordinates are perturbed
by at most `ε`, then `y c < y a`.
-/

/-
**Sharp sufficient condition for top-2 stability.**
If the minimum margin from the excluded class to each member of the top-2 set
exceeds `2ε`, then the top-2 set is stable under `ε`-perturbations.
-/

/-
**Sharp converse: existence of a counterperturbation.**
If one member of a top-2 set has margin at most `2ε` over the excluded class,
there exists an `ε`-perturbation destroying the top-2 property.
-/

/-! ## Section 3: Finite test-family score model and Lipschitz transfer -/



/-
**Lipschitz transfer theorem**: if the score margin exceeds `2 * K * η`,
then the top-2 set is preserved under any `η`-perturbation of test valuations.
-/

/-! ## Section 4: Max-plus linear score model -/



/-
**Max-plus 1-Lipschitz property**: if every test valuation changes by at most `η`,
then every max-plus score changes by at most `η`.
-/

/-
**Max-plus top-2 robustness corollary**: for max-plus score models with test-family
perturbation bounded by `η`, if the margin exceeds `2η` then the top-2 set is stable.
-/


open TropicalSatake in
theorem solution(x : Fin 3 → ℝ) :
    (∃! A : Finset (Fin 3), IsTop2Set x A) ↔
    ∃! c : Fin 3, ∀ i : Fin 3, i ≠ c → x c < x i := by
  constructor;
  · rintro ⟨ A, hA₁, hA₂ ⟩;
    obtain ⟨ c, hc₁, hc₂ ⟩ := card_two_compl_singleton A hA₁.1;
    refine' ⟨ c, _, _ ⟩;
    · exact fun i hi => hA₁.2 i ( by specialize hc₂ i; aesop ) c hc₁;
    · intro y hy; specialize hA₂ ( Finset.univ.erase y ) ; simp_all +decide [ IsTop2Set ] ;
      grind;
  · rintro ⟨ c, hc₁, hc₂ ⟩;
    use Finset.univ.erase c;
    refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
    · fin_cases c <;> trivial;
    · grind;
    · rintro A ⟨ hA₁, hA₂ ⟩;
      fin_cases A <;> simp +decide at hA₁ ⊢;
      · fin_cases c <;> simp +decide [ Fin.forall_fin_succ ] at *;
        · linarith;
        · linarith;
      · fin_cases c <;> simp +decide [ Fin.forall_fin_succ ] at *;
        · linarith;
        · linarith;
      · fin_cases c <;> simp +decide [ Fin.forall_fin_succ ] at *;
        · linarith;
        · linarith
