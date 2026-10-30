-- Prove2me | Theorems.Thm_gpy_secondMoment_assembly_cond
-- name    : gpy_secondMoment_assembly_cond
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-29T21:28:37.827374+00:00
-- url     : https://prove2.me/theorems/e5bb2bfe-4850-4c79-a8da-5445b42c363f
-- title:
--   Conditional GPY assembly: second moment equals its monomial-evaluated main term
-- statement:
--   Let h be a tuple of shifts, R a level with 2 ≤ R, deg a degree, and li a real function, with x ≤ y. Let S₂ be the GPY second moment for the Selberg weight of degree deg. Assume every monomial piece is evaluated by mainMono up to errMono (hypothesis hMono), and the divisor-weighted BV estimate holds at every interval endpoint for the model li/φ (hypothesis hDiv), together with a grouped-bound witness. Then S₂ differs from the coordinate sum of li-differences times the binomial combination of the monomial main terms by at most the hDiv endpoint terms, plus the λ-mass times k, plus the li-difference-weighted binomial combination of the monomial errors. The theorem is conditional on hMono and hDiv, which are hypotheses, not proved here.
-- source:
--   GPY conditional assembly (second moment for the Selberg weight, with the singular sum evaluated by its monomial main terms), formalized from the GPY tuple weight setup, the second-moment BV evaluation, the divisor-weighted BV estimate, and the conditional monomial evaluation

import Mathlib
open Classical

theorem gpy_secondMoment_assembly_cond {k : ℕ} (h : Fin k → ℕ) (R deg : ℕ)
    (hR : 2 ≤ R) (li : ℝ → ℝ) {x y : ℕ} (hxy : x ≤ y)
    (wit : (Fin k → ℕ) → (Fin k → ℕ) → Fin k → ℕ)
    (hwit : ∀ d e i, (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
      Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j)))) →
      (∀ j, Nat.lcm (d j) (e j) ∣ wit d e i + h j) ∧
      Nat.Coprime (wit d e i + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
    (mainMono errMono : Fin k → ℕ → ℕ → ℝ)
    (E : ℕ → ℝ)
    (hMono : ∀ i, ∀ a ∈ Finset.range (deg + 1), ∀ b ∈ Finset.range (deg + 1),
      abs ((∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
        if (∃ w, (∀ j, Nat.lcm (d j) (e j) ∣ w + h j) ∧
            Nat.Coprime (w + h i) (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))))
        then (ArithmeticFunction.moebius (∏ j, d j) : ℝ)
            * (ArithmeticFunction.moebius (∏ j, e j) : ℝ)
            * (-(Real.log ((∏ j, d j : ℕ) : ℝ) / Real.log R)) ^ a
            * (-(Real.log ((∏ j, e j : ℕ) : ℝ) / Real.log R)) ^ b
            / ((Nat.totient (Finset.lcm Finset.univ (fun j => Nat.lcm (d j) (e j))) : ℕ) : ℝ)
        else 0) - mainMono i a b) ≤ errMono i a b)
    (hDiv : ∀ i, (∑ L ∈ Finset.range (R ^ 2 + 1),
          (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
            (fun d => ∏ i, d i = L)).card : ℝ) ^ 2
            * (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (y + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - li ((y + h i : ℕ) : ℝ) / ((Nat.totient L : ℕ) : ℝ)))).Nonempty
              then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (y + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - li ((y + h i : ℕ) : ℝ) / ((Nat.totient L : ℕ) : ℝ)))).max' hne
              else 0)) ≤ E (y + h i) ∧
      (∑ L ∈ Finset.range (R ^ 2 + 1),
          (((Fintype.piFinset (fun _ : Fin (k + 1) => Finset.Icc 1 L)).filter
            (fun d => ∏ i, d i = L)).card : ℝ) ^ 2
            * (if hne : (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (x + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - li ((x + h i : ℕ) : ℝ) / ((Nat.totient L : ℕ) : ℝ)))).Nonempty
              then (((Finset.range L).filter (fun r => Nat.Coprime r L)).image
                (fun r => abs ((((Finset.range (x + h i + 1)).filter
                    (fun p => Nat.Prime p ∧ p ≡ r [MOD L])).card : ℝ)
                  - li ((x + h i : ℕ) : ℝ) / ((Nat.totient L : ℕ) : ℝ)))).max' hne
              else 0)) ≤ E (x + h i)) :
    abs ((∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then
            (if ∏ i, d i ≤ R then
              (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
              else 0)
            else 0) ^ 2)
      - ∑ i, (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
              (deg.choose a : ℝ) * (deg.choose b : ℝ) * mainMono i a b))
      ≤ (∑ i, (E (y + h i) + E (x + h i)))
        + (∑ d ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          ∑ e ∈ (Fintype.piFinset (fun _ : Fin k => Finset.Icc 1 R)).filter (fun d => ∏ i, d i ≤ R),
          abs ((if ∏ i, d i ≤ R then
                (ArithmeticFunction.moebius (∏ i, d i) : ℝ)
                  * (1 - Real.log ((∏ i, d i : ℕ) : ℝ) / Real.log R) ^ deg
                else 0)
              * (if ∏ i, e i ≤ R then
                (ArithmeticFunction.moebius (∏ i, e i) : ℝ)
                  * (1 - Real.log ((∏ i, e i : ℕ) : ℝ) / Real.log R) ^ deg
                else 0))) * (k : ℝ)
        + ∑ i, abs (li ((y + h i : ℕ) : ℝ) - li ((x + h i : ℕ) : ℝ)) *
            (∑ a ∈ Finset.range (deg + 1), ∑ b ∈ Finset.range (deg + 1),
              (deg.choose a : ℝ) * (deg.choose b : ℝ) * errMono i a b) := by sorry
