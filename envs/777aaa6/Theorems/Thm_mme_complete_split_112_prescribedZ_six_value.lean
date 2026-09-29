-- Prove2me | Theorems.Thm_mme_complete_split_112_prescribedZ_six_value
-- name    : mme_complete_split_112_prescribedZ_six_value
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-16T08:01:22.37561+00:00
-- url     : https://prove2.me/theorems/7e52a663-718b-49f3-9df0-3a86e9c87d40
-- title:
--   Prescribed-Z six-value of the canonical q=5 square 112 component
-- statement:
--   Let $T_{112}$ be the canonical $(1,1,2)$ constituent of $\mathrm{CW}_5^{\otimes 2}$ over any field. Choose nonnegative integers $l,g$ satisfying $341l<100g$, and prescribe the exact Z-split counts $(l,2g,l)$ with denominator $D=2(l+g)$. Put $r=l/(2(l+g))$ and let $h$ be the natural-log entropy of $(r,1-2r,r)$.
--
--   For every real $\tau$, the prescribed-Z six-symmetric restriction value has the lower certificate
--   $$
--   \exp\!\left(\frac{h+2\log 2}{3}
--   +\tau\frac{2g+l}{l+g}\log 5\right).
--   $$
--
--   Precisely, every positive strict lower base has finite matrix-multiplication direct-sum witnesses at arbitrarily large compatible indices $m$ and lengths $Dm$, with total $\tau$-weight at least that base raised to $6Dm$. The tensor is the literal canonical component with its canonical Z basis and left fine grade.
--
--   This supplies a component endpoint with the prescribed split retained, so it can be used inside later DWZ tensor powers.
--
--   **Formalization Note** The statement also returns the normalized complete-word profiles realizing the parameter $r$. It is a rational compatible-length restriction certificate; it does not assert a general equivalence with arbitrary real-distribution limsup values.
-- source:
--   Duan, Wu, Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, https://arxiv.org/html/2210.10173v5, Definition 3.9 and Equation (3), Lemma 4.6(d), and its Appendix A proof before optimizing the split parameter. Rational-profile q=5 specialization of the explicit C-tensor restriction construction, under the stronger arithmetic balance hypothesis used by the proved directional-rate interface.

import Definitions.Def_mme_complete_split_112_canonical_source_data
import Definitions.Def_mme_complete_split_112_address_words
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_modern_entropy_data

open MME MME.CompleteSplit MME.CompleteSplit112
open MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open scoped BigOperators NNReal

universe u

set_option autoImplicit false

theorem mme_complete_split_112_prescribedZ_six_value
    {K : Type u} [Field K]
    (l g : ℕ) (hbalance : 341 * l < 100 * g)
    (p : IntegerZSplitProfile 3)
    (hden : p.denominator = 2 * (l + g))
    (hcount : p.count = ![l, 2 * g, l])
    (tau : ℝ) :
    ∃ beta : Fin 3 → Profile 2,
      (∀ mode sigma,
        (beta mode).probability sigma =
          (profileProbability
            ((l : ℚ) / (2 * ((l + g : ℕ) : ℚ))) mode sigma : ℝ)) ∧
      let rateLog : ℝ :=
        Real.log 2 * mme_modern_entropyBits (beta 2).probability +
          2 * Real.log 2 +
          3 * tau *
            (((2 * g + l : ℕ) : ℝ) / ((l + g : ℕ) : ℝ) * Real.log 5)
      HasPrescribedZSixRestrictionValueAtLeast
        (canonicalObj K 5) (canonicalBasis K 5 2)
        (fun x ↦ (canonicalLabel 5 2 x) 0) p tau
        (Real.exp (rateLog / 3)) := by sorry
