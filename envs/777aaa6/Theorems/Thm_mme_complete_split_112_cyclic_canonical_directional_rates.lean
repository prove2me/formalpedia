-- Prove2me | Theorems.Thm_mme_complete_split_112_cyclic_canonical_directional_rates
-- name    : mme_complete_split_112_cyclic_canonical_directional_rates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T04:38:24.120895+00:00
-- url     : https://prove2.me/theorems/f432e635-c6eb-480b-82ab-093293a6101a
-- title:
--   One q=5 star family supplies 112, 121, and 211 complete-profile sources with the same directional rates
-- statement:
--   For naturals $l,g$ with $341l<100g$, set $p=l/(2(l+g))$. There is a normalized complete-profile triple $\beta$ with the exact $112$ word probabilities at $p$, such that for every $\delta>0$ and all sufficiently large $m$, one actual primary-hash family with $N=(l+g)m$, $L=lm$, $G=gm$, outer size $A>0$, and height $H\le4^N$ simultaneously satisfies
--   \[
--   \log A\ge2N\bigl(H_{\mathrm{nat}}(\beta_Z)-\delta\bigr),\qquad
--   \log(AH)\ge2N(\log2-\delta).
--   \]
--   The exact logarithmic side rates are $g\log5/(l+g)$, $l\log5/(l+g)$, and $g\log5/(l+g)$. For every field and nonnegative profile tolerance, the same literal direct sum of actual coupled stars is obtained from the fully filtered canonical $112$ source; its block support and actual $\langle5^{2G},5^{2L},5^{2G}\rangle$ isomorphisms are retained. Moreover, for each $e\in\{\pi,\pi^2\}$,
--   \[
--   e\cdot\bigoplus_a S_a\ \preceq\ F_{\beta\circ e^{-1},\varepsilon}\bigl(T_{112\circ e^{-1}}^{\otimes2N}\bigr).
--   \]
--   These are the literal canonical $211$ and $121$ sources, with their full three-profile filters. Each selected block has the corresponding actual permuted matrix-multiplication isomorphism. The family and the counts are chosen before the field, tolerance, or cyclic orientation; no new counting assertion, value hypothesis, or independent-family intersection is used. The case $l=0$ is included.
-- source:
--   Finite cyclic landing of the already proved parametric actual-family directional rate theorem ceb8e859-d3a2-4251-bd53-929f26f9b934, using the actual canonical CW-square complete-profile cyclic transport. Source motivation: Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, ordered complete-profile Definitions 3.4–3.6, pp. 14–15, https://arxiv.org/abs/2404.16349v2. This theorem supplies rotated literal sources for unequal cyclic star products; it is not the global recursive extraction or numerical surplus.

import Definitions.Def_mme_complete_split_112_address_words
import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_coupled_Ctensor_packaging_data
import Definitions.Def_mme_complete_split_canonical_square_data
import Definitions.Def_mme_permutation
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_112_cyclic_canonical_directional_rates (l g : ℕ) (hbalance : 341 * l < 100 * g) :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma, (beta mode).probability sigma =
        (profileProbability ((l : ℚ) / (2 * ((l + g : ℕ) : ℚ))) mode sigma : ℝ)) ∧
      ∀ delta : ℝ, 0 < delta →
        ∀ᶠ m : ℕ in atTop,
          let N : ℕ := (l + g) * m
          let L : ℕ := l * m
          let G : ℕ := g * m
          ∃ A H : ℕ, ∃ family : CWQ6PrimaryHashFamily N L G A H,
            0 < A ∧ H ≤ 4 ^ N ∧
            ((2 * N : ℕ) : ℝ) *
                (Real.log 2 * mme_modern_entropyBits (beta 2).probability - delta) ≤
              Real.log (A : ℝ) ∧
            ((2 * N : ℕ) : ℝ) * (Real.log 2 - delta) ≤
              Real.log ((A : ℝ) * (H : ℝ)) ∧
            Real.log ((5 ^ (2 * G) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) =
              (g : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5 ∧
            Real.log ((5 ^ (2 * L) : ℕ) : ℝ) / ((2 * N : ℕ) : ℝ) =
              (l : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5 ∧
            ∀ (K : Type u) [Field K] (epsilon : ℝ≥0),
              (TensorObj.Restrict
                  (TensorObj.bigAdd (starObj (grading K 5) family))
                  (restrictedCanonicalPower K 5 beta epsilon (2 * N)) ∧
                ∀ a : Fin A,
                  (∀ sigma : Fin 3 → Fin (H + 1),
                    sigma ∉ Finset.univ.image (cTensorOneHOneAddress H) →
                      (starGrading (grading K 5) family a).blockTensor sigma = 0) ∧
                  ∀ h : Fin H,
                    TensorObj.Isomorphic
                      (MMObj K (5 ^ (2 * G)) (5 ^ (2 * L)) (5 ^ (2 * G)))
                      ((starGrading (grading K 5) family a).blockSubtensor
                        (cTensorOneHOneAddress H h))) ∧
              ∀ (e : Equiv.Perm (Fin 3)),
                e = cyclicPerm ∨ e = cyclicPerm.trans cyclicPerm →
                  TensorObj.Restrict
                    (TensorObj.permObj e
                      (TensorObj.bigAdd (starObj (grading K 5) family)))
                    (CompleteSplitCanonicalSquare.restrictedPower K 5
                      (fun i ↦ cwSquareBlockType 1 1 2 (e.symm i))
                      (fun i ↦ beta (e.symm i)) epsilon (2 * N)) ∧
                  ∀ (a : Fin A) (h : Fin H),
                    TensorObj.Isomorphic
                      (TensorObj.permObj e
                        (MMObj K (5 ^ (2 * G)) (5 ^ (2 * L)) (5 ^ (2 * G))))
                      (TensorObj.permObj e
                        ((starGrading (grading K 5) family a).blockSubtensor
                          (cTensorOneHOneAddress H h))) := by sorry
