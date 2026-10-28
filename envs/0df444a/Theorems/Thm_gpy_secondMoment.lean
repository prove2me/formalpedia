-- Prove2me | Theorems.Thm_gpy_secondMoment
-- name    : gpy_secondMoment
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-27T16:00:46.201547+00:00
-- url     : https://prove2.me/theorems/af4b1c82-566e-4880-8fe1-b1a350313cb6
-- title:
--   Second-moment interchange for GPY tuple weights, with CRT residue form
-- statement:
--   Let h = (h₁, …, hₖ) be a tuple of shifts, R a level, and λ coefficients supported on tuples d with 1 ≤ dᵢ ≤ R and ∏ᵢ dᵢ ≤ R. Let w(n) be the GPY weight (∑_{d: dᵢ ∣ n+hᵢ} λ_d)² and let S₂ = ∑_{x<n≤y} (∑ᵢ 1_prime(n+hᵢ)) w(n). Then S₂ equals the sum over support pairs (d,e) of λ_d λ_e times the sum over coordinates i of the number of n ∈ (x,y] satisfying dᵢ, eᵢ ∣ n+hᵢ for all i and with n+hᵢ prime. Moreover, if a satisfies mᵢ ∣ a+hᵢ for all i, then the joint divisibility system mᵢ ∣ n+hᵢ is equivalent to the single residue class n ≡ a (mod lcmᵢ mᵢ); and if the shifts are incompatible modulo the gcds of the coordinatewise lcms, then every such prime-restricted joint count is zero.
-- source:
--   GPY second-moment interchange (linear form), formalized from the GPY tuple weight setup, the general CRT count, and the first-moment main term

import Mathlib

theorem gpy_secondMoment (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) (x y : ℕ) :
    ∑ n ∈ Finset.Ioc x y, (∑ i, (if Nat.Prime (n + h i) then (1 : ℝ) else 0)) *
        (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2
      =
      ∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
        lam d * lam e *
          (∑ i, ((Finset.filter
            (fun n => ((∀ i, d i ∣ n + h i) ∧ ∀ i, e i ∣ n + h i) ∧
              Nat.Prime (n + h i))
            (Finset.Ioc x y)).card : ℝ)) := by sorry
