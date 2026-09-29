-- Prove2me | solution 1 for mme_released_116_child112_simultaneous_six_weight_rate
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-23T01:03:48.936761+00:00
-- url     : https://prove2.me/submissions/ac2fccb9-b3c0-408c-b719-5d8a28283bd8

import Theorems.Thm_mme_finite_MM_extraction_swap_double
import Theorems.Thm_mme_log_sqrt_loss_eventually_le_linear
import Theorems.Thm_mme_complete_split_112_outer_star_entropy_rate
import Theorems.Thm_mme_central_binomial_sqrt_loss_log_rate
import Definitions.Def_mme_complete_split_112_address_words
import Theorems.Thm_mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
import Theorems.Thm_mme_primary_hash_uniform_stars_joint_directional_capacity
import Theorems.Thm_mme_complete_split_112_coupled_restricted_family_certificate
import Theorems.Thm_mme_complete_split_112_canonical_profile_router
import Theorems.Thm_mme_complete_split_112_canonical_power_restricts_from_intact
import Theorems.Thm_mme_Ctensor_one_H_one_outer_family_direct_finite_extraction
import Definitions.Def_mme_released_116_integer_profiles

open MME MME.CompleteSplit MME.RecursiveYZ MME.Released116
open MME.MoreAsymmetryExactSeed

set_option autoImplicit false

namespace MME.Released116

/-- The released mass of either outer atom in a 112 child. -/
def child112OuterCount (r : Fin 6) : ℕ :=
  ((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
    (0, [], 0)).2.2

/-- Exact marginal counts of the released 112 child, before cell scaling. -/
def child112Marginal (r : Fin 6) (i : Fin 3) (w : CompleteWord 2) : ℕ :=
  if i = 2 then
    if w = ![0, 2] ∨ w = ![2, 0] then child112OuterCount r
    else if w = ![1, 1] then denominator - 2 * child112OuterCount r else 0
  else
    if w = ![0, 1] ∨ w = ![1, 0] then denominator / 2 else 0

/-- All six released parameters lie strictly inside the four-atom family. -/
private theorem mme_released_116_child112_parameter_bounds :
    ∀ r : Fin 6, 0 < child112OuterCount r ∧
      2 * child112OuterCount r < denominator := by
  decide +kernel

/-- The integer reconstruction has uniform X and Y marginals and the exact
three-word Z marginal determined by the released outer-atom count. -/
private theorem mme_released_116_child112_marginal_formula :
    ∀ (r : Fin 6) (c : Split),
      (c.val 0).val = 1 → (c.val 1).val = 1 → (c.val 2).val = 2 →
      ∀ (i : Fin 3) (w : CompleteWord 2),
        childMarginal r c i w = child112Marginal r i w := by
  have h :
      ∀ (r : Fin 6) (i : Fin 3) (w : CompleteWord 2),
        childMarginal r ⟨![1, 1, 2], by decide⟩ i w =
          child112Marginal r i w := by
    decide +kernel
  intro r c h0 h1 h2 i w
  have hc : c = ⟨![1, 1, 2], by decide⟩ := by
    apply Subtype.ext
    funext j
    apply Fin.ext
    fin_cases j
    · exact h0
    · exact h1
    · exact h2
  subst c
  exact h r i w

/-- Cell multiplicity scales the same exact 112 marginal in every mode. -/
private theorem mme_released_116_child112_integer_profile
    (c : Cell 4 6 parent)
    (h0 : (c.2.val 0).val = 1) (h1 : (c.2.val 1).val = 1)
    (h2 : (c.2.val 2).val = 2) (i : Fin 3) (w : CompleteWord 2) :
    integerProfile i c w =
      seed.region.getD c.1.val 0 *
        (splitWeight c.1 c.2 +
          splitWeight c.1 (complement (parent_total c.1) c.2)) *
        denominator * child112Marginal c.1 i w := by
  unfold integerProfile
  rw [mme_released_116_child112_marginal_formula c.1 c.2 h0 h1 h2]

/-- Reversing the two elementary factors preserves every released 112 marginal. -/
private theorem mme_released_116_child112_marginal_reverse :
    ∀ (r : Fin 6) (i : Fin 3) (w : CompleteWord 2),
      child112Marginal r i (fun j => w (Fin.rev j)) = child112Marginal r i w := by
  decide +kernel

/-- The reconstruction is normalized before the physical cell multiplier. -/
private theorem mme_released_116_child112_marginal_mass :
    ∀ (r : Fin 6) (i : Fin 3),
      ∑ w : CompleteWord 2, child112Marginal r i w = denominator := by
  decide +kernel

end MME.Released116


open MME.Released116 MME.CompleteSplit112 Filter

/-- The actual six parameters satisfy the balance condition required by the
uniform induced-family construction. -/
private theorem mme_released_116_child112_hash_balance :
    ∀ r : Fin 6, 341 * (2 * child112OuterCount r) <
      100 * (denominator - 2 * child112OuterCount r) := by
  decide +kernel

/-- The released marginal agrees with the parametric coupled-family profile
at its own exact rational parameter. -/
private theorem mme_released_116_child112_parametric_probability :
    ∀ (r : Fin 6) (i : Fin 3) (w : CompleteWord 2),
      (child112Marginal r i w : ℚ) / denominator =
        profileProbability ((child112OuterCount r : ℚ) / denominator) i w := by
  decide +kernel


/-- Each released region has actual induced families on its exact integer
subsequence, retaining the separate and joint directional capacities. -/
private theorem mme_released_116_child112_cofinal_induced_families (r : Fin 6) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let N := denominator * m
        let L := (2 * child112OuterCount r) * m
        let G := (denominator - 2 * child112OuterCount r) * m
        ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
          0 < A ∧ H ≤ 4 ^ N ∧
          ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
              Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) ∧
          (Nat.choose (2 * N) N : ℝ) *
              Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            4 * (A : ℝ) * (H : ℝ) := by
  let D := denominator
  let l := 2 * child112OuterCount r
  let g := D - l
  have hl : 0 < l := by
    dsimp [l]
    exact Nat.mul_pos (by decide) (mme_released_116_child112_parameter_bounds r).1
  have hsum : l + g = D := by
    have hlt := (mme_released_116_child112_parameter_bounds r).2
    dsimp [l, g, D]
    omega
  have hbalance : 341 * l < 100 * g := mme_released_116_child112_hash_balance r
  obtain ⟨C, hC, hlarge⟩ := mme_CW_q6_primary_hash_uniform_stars_sqrt_loss
    (fun n => l * (n / D)) (fun n => g * (n / D))
  refine ⟨C, hC, ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hlarge
  filter_upwards [eventually_ge_atTop (max N₀ 1)] with m hm
  have hmpos : 0 < m := by omega
  have hNm : N₀ ≤ D * m := by dsimp [D, denominator]; omega
  have hdiv : D * m / D = m := by dsimp [D, denominator]; omega
  have hLpos : 0 < l * m := Nat.mul_pos hl hmpos
  have hLG : l * m + g * m = D * m := by rw [← Nat.add_mul, hsum]
  have hbal : 341 * (l * m) < 100 * (g * m) := by
    simpa only [Nat.mul_assoc] using Nat.mul_lt_mul_of_pos_right hbalance hmpos
  have hextract := hN₀ (D * m) hNm
  dsimp only at hextract
  simp only [hdiv] at hextract
  obtain ⟨A, H, family, hH, hA, hmiddle⟩ := hextract ⟨hLpos, hLG, hbal⟩
  rw [hdiv] at family
  have hcapacity := mme_primary_hash_uniform_stars_joint_directional_capacity
    (D * m) (l * m) (g * m) A H hLG C hA hmiddle
  have hZpos :
      (0 : ℝ) < (Nat.choose (2 * (D * m)) (l * m) *
        Nat.choose (2 * (D * m) - l * m) (l * m) : ℕ) := by
    exact_mod_cast Nat.mul_pos
      (Nat.choose_pos (by omega : l * m ≤ 2 * (D * m)))
      (Nat.choose_pos (by omega : l * m ≤ 2 * (D * m) - l * m))
  have hApos : (0 : ℝ) < A :=
    lt_of_lt_of_le (mul_pos hZpos (Real.exp_pos _)) hA
  exact ⟨A, H, family, by exact_mod_cast hApos, hH, hA, hcapacity.2.2⟩


universe u

/-- A family with the released counts lies in the actual exact-profile
intact 112 tensor, with its full common matrix volume. -/
private theorem mme_released_116_child112_intact_family_certificate
    (r : Fin 6) (m A H : ℕ)
    (family : CWQ6PrimaryHashFamily (denominator * m)
      ((2 * child112OuterCount r) * m)
      ((denominator - 2 * child112OuterCount r) * m) A H)
    (K : Type u) [Field K] :
    Nonempty
      (CTensorOneHOneFamilyCertificate
        (CWCells.unbroken K 5 2 (2 * (denominator * m)) (Equiv.refl _)
          (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
          (fun i _ w => 2 * m * child112Marginal r i w))
        A H (5 ^ (4 * ((denominator - 2 * child112OuterCount r) * m) +
          2 * ((2 * child112OuterCount r) * m)))) := by
  let beta (i : Fin 3) : Profile 2 := {
    level_pos := by decide
    probability w := (child112Marginal r i w : ℝ) / denominator
    nonnegative w := by positivity
    sum_eq_one := by
      rw [← Finset.sum_div, ← Nat.cast_sum, mme_released_116_child112_marginal_mass]
      norm_num [denominator] }
  have hbeta (i : Fin 3) (w : CompleteWord 2) :
      (beta i).probability w =
        (profileProbability ((child112OuterCount r : ℚ) / denominator) i w : ℝ) := by
    dsimp [beta]
    have h := congrArg (fun x : ℚ => (x : ℝ))
      (mme_released_116_child112_parametric_probability r i w)
    simpa only [Rat.cast_div, Rat.cast_natCast] using h
  have hLG :
      (2 * child112OuterCount r) * m +
        (denominator - 2 * child112OuterCount r) * m = denominator * m := by
    rw [← Nat.add_mul, Nat.add_sub_of_le
      (mme_released_116_child112_parameter_bounds r).2.le]
  have hLp :
      (((2 * child112OuterCount r) * m : ℕ) : ℚ) =
        ((2 * (denominator * m) : ℕ) : ℚ) *
          ((child112OuterCount r : ℚ) / denominator) := by
    push_cast
    norm_num [denominator]
    ring
  obtain ⟨certificate⟩ :=
    mme_complete_split_112_coupled_restricted_family_certificate
      (K := K) 5 ((child112OuterCount r : ℚ) / denominator)
      hLG hLp family beta hbeta 0
  have hmu (i : Fin 3) (w : CompleteWord 2) :
      ((2 * m * child112Marginal r i w : ℕ) : ℝ) =
        ((2 * (denominator * m) : ℕ) : ℝ) * (beta i).probability w := by
    dsimp [beta]
    push_cast
    norm_num [denominator]
    ring
  exact ⟨{
    star := certificate.star
    restrict := certificate.restrict.trans
      ((mme_complete_split_112_canonical_profile_router K 5 beta 0
        (2 * (denominator * m))).trans
        (mme_complete_split_112_canonical_power_restricts_from_intact K 5
          (2 * (denominator * m)) beta
          (fun i w => 2 * m * child112Marginal r i w) hmu))
    certificate := certificate.certificate
  }⟩


/-- Cofinal matrix extractions from the actual released exact 112 profiles.
The induced family supplies both directional capacities and the explicit
copy bound after cyclic symmetrization. -/
private theorem mme_released_116_child112_cofinal_matrix_extraction (r : Fin 6) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ m : ℕ in atTop,
        let N := denominator * m
        let L := (2 * (((seed.children.find?
          (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2)) * m
        let G := (denominator - 2 * (((seed.children.find?
          (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2)) * m
        ∃ A H : ℕ, ∃ _family : CWQ6PrimaryHashFamily N L G A H,
          0 < A ∧ H ≤ 4 ^ N ∧
          ((Nat.choose (2 * N) L * Nat.choose (2 * N - L) L : ℕ) : ℝ) *
              Real.exp (-C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤ (A : ℝ) ∧
          (Nat.choose (2 * N) N : ℝ) *
              Real.exp (-2 * C * Real.sqrt ((N + 1 : ℕ) : ℝ)) ≤
            4 * (A : ℝ) * (H : ℝ) ∧
          ∀ (K : Type u) [Field K], ∃ (k : ℕ) (a b c : Fin k → ℕ),
            0 < k ∧
            TensorObj.Restrict
              (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
              (cyclicSymmetrization
                (CWCells.unbroken K 5 2 (2 * N) (Equiv.refl _)
                  (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                  (fun i _ w => 2 * m * childMarginal r ⟨![1, 1, 2], by decide⟩ i w))) ∧
            (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
                Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)))) ≤
              (k : ℝ) ∧
            ∀ j, a j * b j * c j = (5 ^ (4 * G + 2 * L)) ^ 3 := by
  obtain ⟨C, hC, hfamilies⟩ := mme_released_116_child112_cofinal_induced_families r
  refine ⟨C, hC, ?_⟩
  filter_upwards [hfamilies] with m hm
  obtain ⟨A, H, family, hApos, hH, hA, hAH⟩ := hm
  refine ⟨A, H, family, hApos, hH, hA, hAH, ?_⟩
  intro K _
  obtain ⟨certificate⟩ := mme_released_116_child112_intact_family_certificate
    r m A H family K
  obtain ⟨k, a, b, c, hrestrict, hcount, hvolume⟩ :=
    mme_Ctensor_one_H_one_outer_family_direct_finite_extraction certificate family.hHpos
  have hAr : (0 : ℝ) < A := by exact_mod_cast hApos
  have hHr : (0 : ℝ) < H := by exact_mod_cast family.hHpos
  have hpositive : 0 < (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
      Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)))) := by positivity
  have hk : 0 < k := by exact_mod_cast hpositive.trans_le hcount
  refine ⟨k, a, b, c, hk, ?_, hcount, hvolume⟩
  simpa only [mme_released_116_child112_marginal_formula r
    ⟨![1, 1, 2], by decide⟩ rfl rfl rfl] using hrestrict

/-- The released 112 extraction retains the entropy rate of the Z marginal
and both unshared directions, with the explicit final sublinear loss. -/
private theorem mme_released_116_child112_cofinal_matrix_log_rate
    (r : Fin 6) (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ m : ℕ in atTop,
      let N := denominator * m
      let L := (2 * (((seed.children.find?
        (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2)) * m
      let G := (denominator - 2 * (((seed.children.find?
        (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2)) * m
      let p : ℝ := ((((seed.children.find?
        (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD (0, [], 0)).2.2) : ℝ) / denominator
      ∃ A H : ℕ, 0 < A ∧ 0 < H ∧ H ≤ 4 ^ N ∧
        ((2 * N : ℕ) : ℝ) *
            (Real.log 2 * mme_modern_entropyBits ![p, p, 1 - 2 * p] - delta) ≤
          Real.log (A : ℝ) ∧
        ((2 * N : ℕ) : ℝ) * (Real.log 2 - delta) ≤
          Real.log ((A : ℝ) * (H : ℝ)) ∧
        ∀ (K : Type u) [Field K], ∃ (k : ℕ) (a b c : Fin k → ℕ),
          0 < k ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
            (cyclicSymmetrization
              (CWCells.unbroken K 5 2 (2 * N) (Equiv.refl _)
                (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                (fun i _ w => 2 * m * childMarginal r ⟨![1, 1, 2], by decide⟩ i w))) ∧
          (∀ j, a j * b j * c j = (5 ^ (4 * G + 2 * L)) ^ 3) ∧
          ((2 * N : ℕ) : ℝ) *
              (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) -
                3 * delta) -
              100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤ Real.log (k : ℝ) := by
  obtain ⟨C, _hC, hfamilies⟩ := mme_released_116_child112_cofinal_matrix_extraction r
  let l := 2 * child112OuterCount r
  let g := denominator - l
  have hsum : l + g = denominator := by
    exact Nat.add_sub_of_le (mme_released_116_child112_parameter_bounds r).2.le
  have hD : 0 < l + g := by rw [hsum]; decide
  have hp : (l : ℝ) / (2 * (denominator : ℝ)) =
      (child112OuterCount r : ℝ) / denominator := by
    dsimp [l]
    push_cast
    norm_num [denominator]
    ring
  have he := mme_complete_split_112_outer_star_entropy_rate l g hD C delta hdelta
  simp only [hsum, hp] at he
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (mme_central_binomial_sqrt_loss_log_rate C delta hdelta)
  filter_upwards [hfamilies, he, eventually_ge_atTop n₀]
    with m hm hme hmn
  dsimp only at hm hme ⊢
  obtain ⟨A, H, family, hApos, hH, hA, hAH, hextract⟩ := hm
  have hAr : (0 : ℝ) < A := by exact_mod_cast hApos
  have hHr : (0 : ℝ) < H := by exact_mod_cast family.hHpos
  have hNm : n₀ ≤ denominator * m := by dsimp [denominator]; omega
  have hlogAH := hn₀ (denominator * m) hNm
    ((A : ℝ) * (H : ℝ)) (mul_pos hAr hHr)
    (by simpa only [mul_assoc] using hAH)
  have hlogAH' : ((2 * (denominator * m) : ℕ) : ℝ) * (Real.log 2 - delta) ≤
      Real.log ((A : ℝ) * (H : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hlogAH
  have hlogA := hme (A : ℝ) hAr hA
  refine ⟨A, H, hApos, family.hHpos, hH, hlogA, hlogAH', ?_⟩
  intro K _
  obtain ⟨k, a, b, c, hk, hrestrict, hcount, hvolume⟩ := hextract K
  refine ⟨k, a, b, c, hk, hrestrict, hvolume, ?_⟩
  have hpositive : 0 < (A : ℝ) ^ 3 * ((H : ℝ) ^ 2 *
      Real.exp (-100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)))) := by positivity
  have hlog := Real.log_le_log hpositive hcount
  rw [Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, Real.log_exp] at hlog
  rw [Real.log_mul hAr.ne' hHr.ne'] at hlogAH'
  norm_num only [Nat.cast_ofNat] at hlog
  dsimp only [child112OuterCount] at hlogA
  nlinarith only [hlog, hlogA, hlogAH']

namespace MME.Released116

private def child112Split : Split := ⟨![1, 1, 2], by decide⟩

/-- The physical cell multiplier after separating one factor of the
released denominator. Even replication makes the family scale integral. -/
private def child112PhysicalScale (r : Fin 6) : ℕ :=
  seed.region.getD r.val 0 *
    (splitWeight r child112Split +
      splitWeight r (complement (parent_total r) child112Split)) * denominator

private theorem child112_physical_scale_pos :
    ∀ r : Fin 6, 0 < child112PhysicalScale r := by
  decide +kernel

private theorem child112_physical_size (r : Fin 6) (k : ℕ) :
    2 * (denominator * (k * child112PhysicalScale r)) =
      (2 * k) * (splitCount r child112Split +
        splitCount r (complement (parent_total r) child112Split)) := by
  unfold child112PhysicalScale splitCount
  ring

private theorem child112_physical_histogram
    (r : Fin 6) (k : ℕ) (i : Fin 3) (w : CompleteWord 2) :
    2 * (k * child112PhysicalScale r) * childMarginal r child112Split i w =
      (2 * k) * integerProfile i ⟨r, child112Split⟩ w := by
  unfold child112PhysicalScale integerProfile
  ring

end MME.Released116


/-- At every sufficiently large even replication, all six regions admit
the checked 112 extraction on their physical integer profiles. The source
length is the sum of the complementary split multiplicities. -/
private theorem mme_released_116_child112_simultaneous_physical_extraction
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
      let s := (seed.region.getD r.val 0 *
        (splitWeight r (⟨![1, 1, 2], by decide⟩ : Split) +
          splitWeight r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))) * denominator)
      let N := denominator * (k * s)
      let L := (2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2)) * (k * s)
      let G := (denominator - 2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2)) * (k * s)
      let p : ℝ := ((((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2) : ℝ) / denominator
      ∃ A H : ℕ, 0 < A ∧ 0 < H ∧ H ≤ 4 ^ N ∧
        ((2 * N : ℕ) : ℝ) *
            (Real.log 2 * mme_modern_entropyBits ![p, p, 1 - 2 * p] - delta) ≤
          Real.log (A : ℝ) ∧
        ((2 * N : ℕ) : ℝ) * (Real.log 2 - delta) ≤
          Real.log ((A : ℝ) * (H : ℝ)) ∧
        ∀ (K : Type u) [Field K], ∃ (copies : ℕ) (a b c : Fin copies → ℕ),
          0 < copies ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
            (cyclicSymmetrization
              (CWCells.unbroken K 5 2
                ((2 * k) * (splitCount r (⟨![1, 1, 2], by decide⟩ : Split) +
                  splitCount r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))))
                (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                (fun i _ w => (2 * k) * integerProfile i ⟨r, (⟨![1, 1, 2], by decide⟩ : Split)⟩ w))) ∧
          (∀ j, a j * b j * c j = (5 ^ (4 * G + 2 * L)) ^ 3) ∧
          ((2 * N : ℕ) : ℝ) *
              (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) -
                3 * delta) -
              100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
            Real.log (copies : ℝ) := by
  apply Filter.eventually_all.mpr
  intro r
  obtain ⟨m₀, hm₀⟩ := eventually_atTop.1
    (mme_released_116_child112_cofinal_matrix_log_rate r delta hdelta)
  filter_upwards [eventually_ge_atTop m₀] with k hk
  have hscale := child112_physical_scale_pos r
  have hlarge : m₀ ≤ k * child112PhysicalScale r := by nlinarith
  have h := hm₀ (k * child112PhysicalScale r) hlarge
  dsimp only at h ⊢
  obtain ⟨A, H, hA, hH, hHbound, hlogA, hlogAH, hextract⟩ := h
  refine ⟨A, H, hA, hH, hHbound, hlogA, hlogAH, ?_⟩
  intro K _
  obtain ⟨copies, a, b, c, hcopies, hrestrict, hvolume, hrate⟩ := hextract K
  refine ⟨copies, a, b, c, hcopies, ?_, hvolume, hrate⟩
  have hsize := child112_physical_size r k
  have hhist := child112_physical_histogram r k
  dsimp only [child112Split] at hsize hhist
  rw [← hsize]
  simp only [← hhist]
  exact hrestrict


open BigOperators

/-- Swapping and multiplying a cyclic extraction squares its copy count
and common volume. Its logarithmic copy bound gives a six-symmetric weight
bound without requiring the individual matrices to be square. -/
private theorem mme_cyclic_constant_volume_extraction_six_weight
    {K : Type u} [Field K] {T : TensorObj K 3} {k V : ℕ}
    (a b c : Fin k → ℕ) (hk : 0 < k)
    (hrestrict : TensorObj.Restrict
      (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
      (cyclicSymmetrization T))
    (hvolume : ∀ j, a j * b j * c j = V)
    (L tau : ℝ) (hlog : L ≤ Real.log (k : ℝ)) :
    ∃ (copies : ℕ) (a' b' c' : Fin copies → ℕ),
      0 < copies ∧
      TensorObj.Restrict
        (TensorObj.bigAdd (fun j => MMObj K (a' j) (b' j) (c' j)))
        (sixSymmetrization T) ∧
      (∀ j, a' j * b' j * c' j = V ^ 2) ∧
      Real.exp (2 * L) * (((V ^ 2 : ℕ) : ℝ) ^ tau) ≤
        ∑ j, (((a' j * b' j * c' j : ℕ) : ℝ) ^ tau) := by
  let a' := fun r : Fin (k * k) => a (finProdFinEquiv.symm r).1 * c (finProdFinEquiv.symm r).2
  let b' := fun r : Fin (k * k) => b (finProdFinEquiv.symm r).1 * b (finProdFinEquiv.symm r).2
  let c' := fun r : Fin (k * k) => c (finProdFinEquiv.symm r).1 * a (finProdFinEquiv.symm r).2
  have hvol (j : Fin (k * k)) : a' j * b' j * c' j = V ^ 2 := by
    dsimp only [a', b', c']
    calc
      _ = (a (finProdFinEquiv.symm j).1 * b (finProdFinEquiv.symm j).1 *
          c (finProdFinEquiv.symm j).1) *
        (a (finProdFinEquiv.symm j).2 * b (finProdFinEquiv.symm j).2 *
          c (finProdFinEquiv.symm j).2) := by ring
      _ = V ^ 2 := by rw [hvolume, hvolume]; ring
  refine ⟨k * k, a', b', c', Nat.mul_pos hk hk,
    mme_finite_MM_extraction_swap_double a b c hrestrict, hvol, ?_⟩
  simp_rw [hvol]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg (by positivity) _)
  have hkr : (0 : ℝ) < k := by exact_mod_cast hk
  calc
    Real.exp (2 * L) ≤ Real.exp (2 * Real.log (k : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith)
    _ = ((k * k : ℕ) : ℝ) := by rw [two_mul, Real.exp_add, Real.exp_log hkr]; norm_cast


private theorem behrend_log_loss_bound (N H : ℕ) (hH : H ≤ 4 ^ N) :
    100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
      200 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
  have hp : H + 1 ≤ 4 ^ (N + 1) := by
    have hpos : 0 < 4 ^ N := by positivity
    rw [pow_succ]
    omega
  have hlog : Real.log ((H + 1 : ℕ) : ℝ) ≤ 4 * ((N + 1 : ℕ) : ℝ) := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < ((H + 1 : ℕ) : ℝ))
      (show ((H + 1 : ℕ) : ℝ) ≤ (4 : ℝ) ^ (N + 1) by exact_mod_cast hp)
    rw [Real.log_pow] at h
    have hfour : Real.log (4 : ℝ) ≤ 4 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      linarith
    calc
      _ ≤ ((N + 1 : ℕ) : ℝ) * Real.log 4 := h
      _ ≤ ((N + 1 : ℕ) : ℝ) * 4 := mul_le_mul_of_nonneg_left hfour (by positivity)
      _ = _ := mul_comm _ _
  have hl0 : 0 ≤ Real.log ((H + 1 : ℕ) : ℝ) := Real.log_nonneg (by norm_cast; omega)
  have hs : Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤
      2 * Real.sqrt ((N + 1 : ℕ) : ℝ) := by
    nlinarith [Real.sq_sqrt hl0,
      Real.sq_sqrt (show (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) by positivity),
      Real.sqrt_nonneg (Real.log ((H + 1 : ℕ) : ℝ)),
      Real.sqrt_nonneg ((N + 1 : ℕ) : ℝ)]
  linarith


/-- The final square-root loss can be absorbed in any positive entropy
budget, uniformly across the six physical regions. -/
private theorem child112_physical_clean_log_rate (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
      let N := denominator * (k * child112PhysicalScale r)
      let L := (2 * child112OuterCount r) * (k * child112PhysicalScale r)
      let G := (denominator - 2 * child112OuterCount r) * (k * child112PhysicalScale r)
      let p : ℝ := (child112OuterCount r : ℝ) / denominator
      ∀ (K : Type u) [Field K], ∃ (copies : ℕ) (a b c : Fin copies → ℕ),
        0 < copies ∧
        TensorObj.Restrict
          (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
          (cyclicSymmetrization
            (CWCells.unbroken K 5 2
              ((2 * k) * (splitCount r child112Split +
                splitCount r (complement (parent_total r) child112Split)))
              (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
              (fun i _ w => (2 * k) * integerProfile i ⟨r, child112Split⟩ w))) ∧
        (∀ j, a j * b j * c j = (5 ^ (4 * G + 2 * L)) ^ 3) ∧
        ((2 * N : ℕ) : ℝ) *
          (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) ≤
          Real.log (copies : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1
    (mme_log_sqrt_loss_eventually_le_linear 0 200 0 delta hdelta)
  filter_upwards [mme_released_116_child112_simultaneous_physical_extraction
    (delta / 6) (by positivity), eventually_ge_atTop n₀] with k hk hkn
  intro r
  have hs := child112_physical_scale_pos r
  have hd : 0 < denominator := by decide
  have hlarge : n₀ ≤ denominator * (k * child112PhysicalScale r) := by
    calc
      n₀ ≤ k := hkn
      _ ≤ k * child112PhysicalScale r := by nlinarith
      _ ≤ denominator * (k * child112PhysicalScale r) := by
        simpa only [one_mul] using
          Nat.mul_le_mul_right (k * child112PhysicalScale r) (show 1 ≤ denominator from hd)
  have hbudget := hn₀ _ hlarge
  have h := hk r
  dsimp only at h ⊢
  obtain ⟨A, H, hA, hH, hHbound, hlogA, hlogAH, hextract⟩ := h
  intro K _
  obtain ⟨copies, a, b, c, hcopies, hrestrict, hvolume, hrate⟩ := hextract K
  refine ⟨copies, a, b, c, hcopies, hrestrict, hvolume, ?_⟩
  change H ≤ 4 ^ (denominator * (k * child112PhysicalScale r)) at hHbound
  have hloss := behrend_log_loss_bound _ H hHbound
  change ((2 * (denominator * (k * child112PhysicalScale r)) : ℕ) : ℝ) *
    (Real.log 2 * (mme_modern_entropyBits
      ![(child112OuterCount r : ℝ) / denominator,
        (child112OuterCount r : ℝ) / denominator,
        1 - 2 * ((child112OuterCount r : ℝ) / denominator)] + 2) - 3 * (delta / 6)) -
      100 * Real.sqrt (Real.log ((H + 1 : ℕ) : ℝ)) ≤ Real.log (copies : ℝ) at hrate
  change H ≤ 4 ^ (denominator * (k * child112PhysicalScale r)) at hHbound
  simp only [zero_mul, zero_add, add_zero] at hbudget
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat] at hloss hbudget hrate ⊢
  nlinarith only [hrate, hloss, hbudget]


/-- All six released physical 112 cells attain their entropy and volume
rate after six-symmetrization, with any positive finite rate allowance. -/
theorem solution
    (delta : ℝ) (hdelta : 0 < delta) :
    ∀ᶠ k : ℕ in atTop, ∀ r : Fin 6,
      let s := (seed.region.getD r.val 0 *
        (splitWeight r (⟨![1, 1, 2], by decide⟩ : Split) +
          splitWeight r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))) * denominator)
      let N := denominator * (k * s)
      let L := (2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2)) * (k * s)
      let G := (denominator - 2 * (((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2)) * (k * s)
      let D := 4 * G + 2 * L
      let p : ℝ := ((((seed.children.find? (fun c => c.1 == r.val && c.2.1 == [1, 1, 2])).getD
        (0, [], 0)).2.2) : ℝ) / denominator
      ∀ (K : Type u) [Field K] (tau : ℝ),
        ∃ (copies : ℕ) (a b c : Fin copies → ℕ),
          0 < copies ∧
          TensorObj.Restrict
            (TensorObj.bigAdd (fun j => MMObj K (a j) (b j) (c j)))
            (sixSymmetrization
              (CWCells.unbroken K 5 2
                ((2 * k) * (splitCount r (⟨![1, 1, 2], by decide⟩ : Split) +
                  splitCount r (complement (parent_total r) (⟨![1, 1, 2], by decide⟩ : Split))))
                (Equiv.refl _) (fun _ => Unit.unit) (fun _ => ![1, 1, 2])
                (fun i _ w => (2 * k) * integerProfile i ⟨r, (⟨![1, 1, 2], by decide⟩ : Split)⟩ w))) ∧
          (∀ j, a j * b j * c j = 5 ^ (6 * D)) ∧
          Real.exp (((4 * N : ℕ) : ℝ) *
              (Real.log 2 * (mme_modern_entropyBits ![p, p, 1 - 2 * p] + 2) - delta) +
            ((6 * D : ℕ) : ℝ) * tau * Real.log 5) ≤
            ∑ j, (((a j * b j * c j : ℕ) : ℝ) ^ tau) := by
  filter_upwards [child112_physical_clean_log_rate delta hdelta] with k hk
  intro r
  dsimp only
  intro K _ tau
  obtain ⟨copies, a, b, c, hcopies, hrestrict, hvolume, hlog⟩ := hk r K
  obtain ⟨count, a', b', c', hcount, hrestrict', hvolume', hweight⟩ :=
    mme_cyclic_constant_volume_extraction_six_weight a b c hcopies
      hrestrict hvolume _ tau hlog
  dsimp only [child112PhysicalScale, child112OuterCount, child112Split] at hvolume' hweight
  refine ⟨count, a', b', c', hcount, hrestrict', ?_, ?_⟩
  · intro j
    rw [hvolume', ← pow_mul, ← pow_mul]
    congr 1
    ring
  · have hweight_eq (D : ℕ) :
        (((((5 ^ D) ^ 3) ^ 2 : ℕ) : ℝ) ^ tau) =
          Real.exp (((6 * D : ℕ) : ℝ) * tau * Real.log 5) := by
      rw [Real.rpow_def_of_pos (by positivity)]
      push_cast
      simp only [Real.log_pow]
      congr 1
      ring
    rw [hweight_eq, ← Real.exp_add] at hweight
    convert hweight using 1
    congr 1
    push_cast
    ring


#print axioms solution
