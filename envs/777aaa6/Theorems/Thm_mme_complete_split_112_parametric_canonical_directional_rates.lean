-- Prove2me | Theorems.Thm_mme_complete_split_112_parametric_canonical_directional_rates
-- name    : mme_complete_split_112_parametric_canonical_directional_rates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-07T00:33:25.46647+00:00
-- url     : https://prove2.me/theorems/ceb8e859-d3a2-4251-bd53-929f26f9b934
-- title:
--   Rational 112 profiles in the hashing range have same-family canonical directional rates
-- statement:
--   Let $l,g$ be nonnegative integers with $341l<100g$, and set $D=l+g$, $p=l/(2D)$. There is one normalized triple $\beta$ of complete 112 profiles: the X and Y profiles each have two masses $1/2,1/2$, and the Z profile has masses $p,p,1-2p$.
--
--   For every $\delta>0$ and all sufficiently large integers $m$, put $N=Dm$, $L=lm$, and $G=gm$. There is one actual primary hash family with outer count $A>0$ and fiber size $H\le 4^N$, whose counts satisfy
--   $
--   \log A\ge 2N\bigl((\log 2)\operatorname{entropyBits}(\beta_Z)-\delta\bigr),
--   \qquad
--   \log(AH)\ge 2N(\log 2-\delta).
--   $
--   The exact component side-log rates are
--   $
--   \frac{\log 5^{2G}}{2N}=\frac gD\log 5,\qquad
--   \frac{\log 5^{2L}}{2N}=\frac lD\log 5.
--   $
--
--   For every field and every nonnegative profile tolerance, the literal direct sum of this same family's stars restricts from the actual canonical CW5-square 112 power filtered by all three profiles. Each star has actual $C_{\langle1,H,1\rangle}$ support, and every component is isomorphic to the matrix-multiplication tensor $\langle5^{2G},5^{2L},5^{2G}\rangle$.
--
--   The result includes $l=0$. This is an unrotated directional interface; it does not assert a scalar tensor value or a global exponent bound.
-- source:
--   A formal composition of the actual finite primary-hash extraction and the112 split analysis in Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Section6.3 (printed pp58–59), https://arxiv.org/abs/2210.10173v5, with the complete-word profiles and all-mode filtered tensor definition in Alman et al., More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Definitions3.4–3.6 (printed pp14–15), https://arxiv.org/abs/2404.16349v2. It reuses proved uniform-star square-root-loss bounds, the exact joint directional capacity identity, and proved multinomial/central-binomial logarithmic rate estimates. The zero-profile endpoint is constructed by complementary half-size subsets, not inferred by continuity. This exact packaged statement is a new formal adapter rather than a separately numbered source theorem.

import Definitions.Def_mme_complete_split_112_address_words
import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_complete_split_112_coupled_grading_data
import Definitions.Def_mme_coupled_Ctensor_packaging_data
import Definitions.Def_mme_modern_entropy_data
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open MME MME.CompleteSplit MME.CompleteSplit112 Filter
open CoupledCTensorPackaging
open scoped NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_112_parametric_canonical_directional_rates (l g : ℕ) (hbalance : 341 * l < 100 * g) :
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
              TensorObj.Restrict
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
                      (cTensorOneHOneAddress H h)) := by sorry
