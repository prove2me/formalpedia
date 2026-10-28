-- Prove2me | Theorems.Thm_gpy_firstMoment_mainTerm
-- name    : gpy_firstMoment_mainTerm
-- status  : Proved
-- author  : @pitimespi
-- created : 2026-10-27T13:49:28.509501+00:00
-- url     : https://prove2.me/theorems/b5397398-1484-41df-bdfa-0258818c1fa9
-- title:
--   First-moment main term for GPY tuple weights, general-compatibility version
-- statement:
--   Let k be a positive integer, h : Fin k → ℕ a tuple of shifts, R a level, and λ : (Fin k → ℕ) → ℝ coefficients supported on tuples d with 1 ≤ d i ≤ R and ∏ d i ≤ R. Define the GPY weight w(n) = (∑_d λ_d)², summed over support tuples d with d i ∣ n + h i at every coordinate. Then for x ≤ y, the first moment ∑_{x<n≤y} w(n) equals (y−x) times the sum of λ_d λ_e / L(d,e) over compatible support pairs (d,e) — those with h i ≡ h j mod gcd(lcm(d i,e i), lcm(d j,e j)) for all i,j, where L(d,e) is the lcm of all lcm(d i,e i) — up to an error of at most the sum of |λ_d λ_e| over the compatible pairs. Incompatible pairs contribute exactly 0 to both the moment and the main term.
-- source:
--   GPY first-moment main term (general-compatibility version), formalized from the GPY tuple weight setup and the general CRT count

import Mathlib

theorem gpy_firstMoment_mainTerm (k : ℕ) (h : Fin k → ℕ) (R : ℕ)
    (lam : (Fin k → ℕ) → ℝ) {x y : ℕ} (hxy : x ≤ y) :
    abs (∑ n ∈ Finset.Ioc x y,
        (∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          if (∀ i, d i ∣ n + h i) then lam d else 0) ^ 2
      - ((y : ℝ) - x) * ∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
            (fun d => ∏ i, d i ≤ R),
          (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
              h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
           then lam d * lam e /
             Finset.lcm Finset.univ (fun i => Nat.lcm (d i) (e i))
           else 0))
    ≤ ∑ d ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        ∑ e ∈ (Fintype.piFinset (fun _ => Finset.Icc 1 R)).filter
          (fun d => ∏ i, d i ≤ R),
        (if (∀ i ∈ Finset.univ, ∀ j ∈ Finset.univ,
              h i ≡ h j [MOD Nat.gcd (Nat.lcm (d i) (e i)) (Nat.lcm (d j) (e j))])
         then abs (lam d * lam e) else 0) := by sorry
