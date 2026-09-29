-- Prove2me | Theorems.Thm_mme_recursive_thin_regional_induced_families_below_marginal_rate
-- name    : mme_recursive_thin_regional_induced_families_below_marginal_rate
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-18T15:53:05.481819+00:00
-- url     : https://prove2.me/theorems/3e522067-79f2-4ed6-8e6a-beaa8dc85ffc
-- title:
--   Actual thin regional induced families at every rate below the minimum summed marginal entropy
-- statement:
--   Let there be finitely many regions r, with parent grade vectors P_r in N^3, each having at least one coordinate at most 1. A split in region r is a vector a in {0,...,4}^3 with coordinate sum 4 and a_i <= P_{r,i}. Choose nonnegative integer split multiplicities m_r(a) with total n_r in region r, and suppose the sum of all n_r is positive. Define the marginal multiplicities and their mass entropies, using natural logarithms and 0 log 0 = 0, by
--   $$
--   M_{r,i,j}=\sum_{a:a_i=j}m_r(a),\qquad
--   H_i=\sum_r\left(n_r\log n_r-\sum_jM_{r,i,j}\log M_{r,i,j}\right).
--   $$
--   For every nonnegative real rate rho strictly below min(H_X,H_Y,H_Z), and every sufficiently large integer t, there is a set E_t of split addresses w_r:[tn_r] -> {admissible splits}, each having exact split counts t m_r, such that
--   $$
--   |E_t|\ge \exp(\rho t).
--   $$
--   The coordinate-word projection is injective on E_t in each of the three modes. Moreover, whenever x,y,z belong to E_t and their mixed coordinate grades satisfy
--   $$
--   x_r(s)_X+y_r(s)_Y+z_r(s)_Z=4
--   \quad\text{for every region }r\text{ and position }s,
--   $$
--   one has x=y=z. Thus the selected addresses form an induced family, not just a matching inside the target type.
--
--   The rate is the minimum of the three entropy sums over ALL regions. The result constructs the necessary prime, progression-free labels, common hash state and isolated family; none is assumed. It is the classical coarse counting step useful for T116's six-region extraction. Translating its induced family into tensor maps and proving the component's value remain separate steps.
-- source:
--   Duan, Wu and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, https://arxiv.org/html/2210.10173v5#S7. A sufficient classical coarse-selection specialization for thin parent regions in Section 7, using exact prescribed split types and progression-free hashing. Derived generic supporting theorem, not a verbatim numbered claim.

import Definitions.Def_mme_recursive_x_hash_families
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.Field

open BigOperators Filter MME.RecursiveThinSplit MME.RecursiveXHash
open scoped Classical Topology
set_option autoImplicit false

theorem mme_recursive_thin_regional_induced_families_below_marginal_rate (R : ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hthin : ∀ r, ∃ i, parent r i ≤ 1)
    (n : Fin R → ℕ) (m : ∀ r, Split 4 (parent r) → ℕ)
    (hm : ∀ r, ∑ a, m r a = n r) (hn : 0 < ∑ r, n r) :
    let M := fun (r : Fin R) (i : Fin 3) (j : Fin 5) ↦
      ∑ a : {a : Split 4 (parent r) // a.val i = j}, m r a.val
    let HM := fun i : Fin 3 ↦ ∑ r,
      (((∑ j, M r i j : ℕ) : ℝ) * Real.log ((∑ j, M r i j : ℕ) : ℝ) -
        ∑ j, (M r i j : ℝ) * Real.log (M r i j : ℝ))
    ∀ ρ : ℝ, 0 ≤ ρ → ρ < min (min (HM 0) (HM 1)) (HM 2) →
      ∀ᶠ t : ℕ in atTop,
        ∃ kept : Finset (Address 4 R parent (fun r ↦ n r * t)),
          kept ⊆ target (fun r a ↦ m r a * t) ∧
          (∀ i : Fin 3, Function.Injective (fun a : kept ↦ block i a.val)) ∧
          (∀ x y z : kept,
            (∀ r s, ((x.val r s).val 0).val + ((y.val r s).val 1).val +
              ((z.val r s).val 2).val = 4) → x = y ∧ y = z) ∧
          Real.exp (ρ * (t : ℝ)) ≤ (kept.card : ℝ) := by sorry
