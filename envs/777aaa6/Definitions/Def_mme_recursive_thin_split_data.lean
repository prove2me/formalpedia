-- Prove2me | Definitions.Def_mme_recursive_thin_split_data
-- name    : mme_recursive_thin_split_data
-- status  : Definition
-- author  : @raresbuhai
-- created : 2026-09-11T22:08:23.818867+00:00
-- url     : https://prove2.me/theorems/251b2696-c473-4236-a4dc-298985b0d773
-- title:
--   Admissible recursive split supports, exact histograms, and entropy penalty
-- statement:
--   For a half-grade $h$ and parent grade triple $p$, this module defines the finite support
--
--   $$S_h(p)=\{a\in\{0,\ldots,h\}^3:a_0+a_1+a_2=h,\ a_i\le p_i\text{ for all }i\}.$$
--
--   The complementary half has grades $p-a$. In the physical recursive application, the parent total is $2h$; the definitions themselves also allow arbitrary parents. They record integer word counts, joint-count and induced marginal-count predicates, and the probability distributions sharing a prescribed set of coordinate marginals. The entropy penalty is the supremum of their bit entropies minus the prescribed bit entropy.
--
--   These are definitions only. No marginal uniqueness, counting equality, entropy bound, or tensor extraction is assumed. Coordinate marginals and bit entropy reuse the existing modern entropy interface.
-- source:
--   New auxiliary lemma derived from the admissible recursive split support in Alman, Duan, Vassilevska Williams, Xu, Xu, Zhou, More Asymmetry Yields Faster Matrix Multiplication, arXiv:2404.16349v2, Section 6 (Table 3), Proposition 6.3, and Section 6.2, Claim 6.6; https://arxiv.org/html/2404.16349v2#S6. This structural simplification is not asserted as a separately numbered theorem in the paper.

import Definitions.Def_mme_modern_entropy_data
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.Pi

open BigOperators

set_option autoImplicit false

namespace MME.RecursiveThinSplit

/-- Admissible left-half grades. The right-half grades are parent minus left.
For a recursive fourth-power component, half = 4 and the parent sums to 8. -/
abbrev Split (half : ℕ) (parent : Fin 3 → ℕ) :=
  {a : Fin 3 → Fin (half + 1) //
    (a 0).val + (a 1).val + (a 2).val = half ∧
    ∀ i, (a i).val ≤ parent i}

/-- Number of occurrences of one symbol in a word, including the empty word. -/
def count {A : Type*} [DecidableEq A] {n : ℕ} (w : Fin n → A) (a : A) : ℕ :=
  (Finset.univ.filter (fun j ↦ w j = a)).card

/-- Exact joint type, in unnormalized integer counts. -/
def HasJointCounts {half n : ℕ} {parent : Fin 3 → ℕ}
    (w : Fin n → Split half parent) (m : Split half parent → ℕ) : Prop :=
  ∀ a, count w a = m a

/-- Exact coordinate histograms induced by the prescribed joint counts. -/
def HasMarginalCounts {half n : ℕ} {parent : Fin 3 → ℕ}
    (w : Fin n → Split half parent) (m : Split half parent → ℕ) : Prop :=
  ∀ (i : Fin 3) (j : Fin (half + 1)),
    count (fun t ↦ (w t).val i) j =
      ∑ a : {a : Split half parent // a.val i = j}, m a.val

/-- Distributions with the same physical coordinate marginals as alpha. -/
def SameMarginalDistributions {half : ℕ} {parent : Fin 3 → ℕ}
    (alpha : Split half parent → ℝ) : Set (Split half parent → ℝ) :=
  {rho | (∀ a, 0 ≤ rho a) ∧ (∑ a, rho a = 1) ∧
    ∀ (i : Fin 3) (j : Fin (half + 1)),
      mme_modern_marginal (fun a ↦ a.val i) rho j =
      mme_modern_marginal (fun a ↦ a.val i) alpha j}

/-- The recursive maximum-entropy penalty in bits, as in More Asymmetry Table 3. -/
noncomputable def entropyPenalty {half : ℕ} {parent : Fin 3 → ℕ}
    (alpha : Split half parent → ℝ) : ℝ :=
  sSup (mme_modern_entropyBits '' SameMarginalDistributions alpha) -
    mme_modern_entropyBits alpha

end MME.RecursiveThinSplit


