-- Prove2me | Theorems.Thm_gpy_secondMoment_bvInst_uncond
-- name    : gpy_secondMoment_bvInst_uncond
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-28T23:16:17.130985+00:00
-- url     : https://prove2.me/theorems/dc067618-28f3-4eb6-ba12-70e9d42d1e2a
-- title:
--   BV instantiation for the GPY second moment: unconditional error bound from Bombieri–Vinogradov
-- statement:
--   Let h be a tuple of shifts, R a level, and λ coefficients supported on tuples d with 1 ≤ dᵢ ≤ R and ∏ᵢ dᵢ ≤ R. Let S₂ be the GPY second moment and let Λ = ∑_{d,e} |λ_d λ_e| be the total λ-mass. Let A' > 0 and η > 0, and assume the level constraint R² < Y^{1/2−η} with 2 ≤ Y' at every interval endpoint y + hᵢ, x + hᵢ. Then for x ≤ y, there is a constant C ≥ 0 (the Bombieri–Vinogradov constant for A' and η) such that S₂ differs from the main-term sum for the model Li/φ (λ_d λ_e times the model differences Li(y+hᵢ)/φ(L) − Li(x+hᵢ)/φ(L), summed over good support pairs, where Li is the logarithmic integral and L is the combined modulus) by at most Λ · (R² · ∑ᵢ (C·(y+hᵢ)·log(y+hᵢ)^{−A'} + C·(x+hᵢ)·log(x+hᵢ)^{−A'}) + k). Unlike the conditional form, the BV-style sum bounds are not hypotheses here: they are discharged from the Bombieri–Vinogradov theorem, and the level bound L ≤ R² for support pairs puts every combined modulus inside the BV range.
-- source:
--   GPY second-moment BV instantiation (unconditional error bound from Bombieri–Vinogradov), formalized from the GPY tuple weight setup, the general CRT count, the first-moment main term, the second-moment interchange, the second-moment BV evaluation, and the second-moment BV error control, with the BV input supplied by ArtinPrimitiveRoots.bombieri_vinogradov

import Mathlib
import Definitions.Def_ArtinSieve
open Classical

theorem gpy_secondMoment_bvInst_uncond {k : ℕ} (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) {x y : ℕ} (hxy : x ≤ y)
    {η A' : ℝ} (hA' : 0 < A') (hη : 0 < η)
    (hlevel : ∀ i, (R : ℝ) ^ 2 < ((y + h i : ℕ) : ℝ) ^ (1 / 2 - η) ∧
      (R : ℝ) ^ 2 < ((x + h i : ℕ) : ℝ) ^ (1 / 2 - η))
    (hY2 : ∀ i, 2 ≤ y + h i ∧ 2 ≤ x + h i) :
    ∃ C : ℝ, 0 ≤ C ∧
    abs (∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2
      - ∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        lam d * lam e *
          (∑ i, if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
              Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
            then ArtinPrimitiveRoots.logIntegral ((y + h i : ℕ) : ℝ) / (Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ)
              - ArtinPrimitiveRoots.logIntegral ((x + h i : ℕ) : ℝ) / (Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℝ)
            else 0))
    ≤ (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        abs (lam d * lam e))
      * ((R : ℝ) ^ 2 * (∑ i, (C * (((y + h i : ℕ) : ℝ) * Real.log ((y + h i : ℕ) : ℝ) ^ (-A'))
          + C * (((x + h i : ℕ) : ℝ) * Real.log ((x + h i : ℕ) : ℝ) ^ (-A')))) + (k : ℝ)) := by sorry
