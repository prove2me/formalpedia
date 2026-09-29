-- Prove2me | solution 1 for mme_stothers_lemma52_same_marginal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T18:52:46.685751+00:00
-- url     : https://prove2.me/submissions/2a92a4ba-03c0-47a5-a196-3129dd27c980

import Definitions.Def_mme_stothers_fourth_data
import Theorems.Thm_mme_modern_entropyBits_additive_certificate

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 1000000

namespace MME.StothersFourth


/-- The finite type of fourth-power grade triples whose entries sum to eight. -/
abbrev SupportTriple :=
  {sigma : Fin 3 → Fin 9 // (∑ s, (sigma s).val) = 8}

/-- A computational presentation of the six possible permutations of three
coordinates. -/
def sameOrbitExplicit (sigma rho : Fin 3 → Fin 9) : Prop :=
  (sigma 0 = rho 0 ∧ sigma 1 = rho 1 ∧ sigma 2 = rho 2) ∨
  (sigma 0 = rho 0 ∧ sigma 1 = rho 2 ∧ sigma 2 = rho 1) ∨
  (sigma 0 = rho 1 ∧ sigma 1 = rho 0 ∧ sigma 2 = rho 2) ∨
  (sigma 0 = rho 1 ∧ sigma 1 = rho 2 ∧ sigma 2 = rho 0) ∨
  (sigma 0 = rho 2 ∧ sigma 1 = rho 0 ∧ sigma 2 = rho 1) ∨
  (sigma 0 = rho 2 ∧ sigma 1 = rho 1 ∧ sigma 2 = rho 0)

instance instDecidableSameOrbitExplicit (sigma rho : Fin 3 → Fin 9) :
    Decidable (sameOrbitExplicit sigma rho) := by
  unfold sameOrbitExplicit
  infer_instance

private def perm012 : Equiv.Perm (Fin 3) :=
  Equiv.refl (Fin 3)

private def perm021 : Equiv.Perm (Fin 3) :=
  Equiv.swap 1 2

private def perm102 : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 1

private def perm120 : Equiv.Perm (Fin 3) :=
  (Equiv.swap 0 1).trans (Equiv.swap 0 2)

private def perm201 : Equiv.Perm (Fin 3) :=
  (Equiv.swap 0 2).trans (Equiv.swap 0 1)

private def perm210 : Equiv.Perm (Fin 3) :=
  Equiv.swap 0 2

/-- On three coordinates, the abstract permutation-orbit relation is exactly
the explicit disjunction of its six possible coordinate arrangements. -/
theorem sameOrbit_iff_explicit (sigma rho : Fin 3 → Fin 9) :
    sameOrbit sigma rho ↔ sameOrbitExplicit sigma rho := by
  constructor
  · rintro ⟨e, he⟩
    have h01 : e 0 ≠ e 1 := by
      intro h
      have := e.injective h
      omega
    have h02 : e 0 ≠ e 2 := by
      intro h
      have := e.injective h
      omega
    have h12 : e 1 ≠ e 2 := by
      intro h
      have := e.injective h
      omega
    obtain ⟨e0, h0⟩ : ∃ e0 : Fin 3, e 0 = e0 := ⟨e 0, rfl⟩
    obtain ⟨e1, h1⟩ : ∃ e1 : Fin 3, e 1 = e1 := ⟨e 1, rfl⟩
    obtain ⟨e2, h2⟩ : ∃ e2 : Fin 3, e 2 = e2 := ⟨e 2, rfl⟩
    fin_cases e0 <;>
      fin_cases e1 <;>
      fin_cases e2 <;>
      simp_all [sameOrbitExplicit]
  · intro h
    rcases h with h | h | h | h | h | h
    · rcases h with ⟨h0, h1, h2⟩
      refine ⟨perm012, ?_⟩
      intro s
      fin_cases s <;> simp_all [perm012]
    · rcases h with ⟨h0, h1, h2⟩
      refine ⟨perm021, ?_⟩
      intro s
      fin_cases s <;> simp_all [perm021, Equiv.swap_apply_def]
    · rcases h with ⟨h0, h1, h2⟩
      refine ⟨perm102, ?_⟩
      intro s
      fin_cases s <;> simp_all [perm102, Equiv.swap_apply_def]
    · rcases h with ⟨h0, h1, h2⟩
      refine ⟨perm120, ?_⟩
      intro s
      fin_cases s <;> simp_all [perm120, Equiv.swap_apply_def]
    · rcases h with ⟨h0, h1, h2⟩
      refine ⟨perm201, ?_⟩
      intro s
      fin_cases s <;> simp_all [perm201, Equiv.swap_apply_def]
    · rcases h with ⟨h0, h1, h2⟩
      refine ⟨perm210, ?_⟩
      intro s
      fin_cases s <;> simp_all [perm210, Equiv.swap_apply_def]

/-- There are exactly 45 ordered triples of grades in `{0, ..., 8}` whose
sum is eight. -/
theorem supportTriple_card : Fintype.card SupportTriple = 45 := by
  decide

/-- Every supported grade triple belongs to exactly one of the ten displayed
permutation classes. -/
theorem supportTriple_unique_class :
    ∀ sigma : SupportTriple,
      ∃! r : Fin 10, sameOrbit sigma.1 (classRep r) := by
  have hExists :
      ∀ sigma : SupportTriple,
        ∃ r : Fin 10, sameOrbitExplicit sigma.1 (classRep r) := by
    decide
  have hAtMostOne :
      ∀ (sigma : SupportTriple) (r₁ r₂ : Fin 10),
        sameOrbitExplicit sigma.1 (classRep r₁) →
          sameOrbitExplicit sigma.1 (classRep r₂) → r₁ = r₂ := by
    decide
  intro sigma
  rcases hExists sigma with ⟨r, hr⟩
  refine ⟨r, (sameOrbit_iff_explicit _ _).mpr hr, ?_⟩
  intro y hy
  exact hAtMostOne sigma y r ((sameOrbit_iff_explicit _ _).mp hy) hr

/-- The orbit of each displayed representative has the multiplicity recorded
in Table 1. -/
theorem supportTriple_orbit_card :
    ∀ r : Fin 10,
      Fintype.card
          {sigma : SupportTriple // sameOrbit sigma.1 (classRep r)} =
        3 * classMultiplicity r := by
  have hExplicit :
      ∀ r : Fin 10,
        Fintype.card
            {sigma : SupportTriple //
              sameOrbitExplicit sigma.1 (classRep r)} =
          3 * classMultiplicity r := by
    decide
  intro r
  rw [← hExplicit r]
  apply Fintype.card_congr
  exact
    { toFun := fun sigma ↦
        ⟨sigma.1, (sameOrbit_iff_explicit _ _).mp sigma.2⟩
      invFun := fun sigma ↦
        ⟨sigma.1, (sameOrbit_iff_explicit _ _).mpr sigma.2⟩
      left_inv := fun sigma ↦ Subtype.ext rfl
      right_inv := fun sigma ↦ Subtype.ext rfl }

end MME.StothersFourth

/-- The two vectors displayed after Equation (5.2) span exactly the kernel
of the marginal map `Q`. -/
theorem mme_stothers_Q_kernel_eq_span :
    ∀ x : Fin 10 → ℝ,
      (∀ j : Fin 9, MME.StothersFourth.Q x j = 0) ↔
        MME.StothersFourth.InY x := by
  intro x
  constructor
  · intro hQ
    have h0 := hQ (0 : Fin 9)
    have h1 := hQ (1 : Fin 9)
    have h2 := hQ (2 : Fin 9)
    have h3 := hQ (3 : Fin 9)
    have h4 := hQ (4 : Fin 9)
    have h5 := hQ (5 : Fin 9)
    have h6 := hQ (6 : Fin 9)
    have h7 := hQ (7 : Fin 9)
    have h8 := hQ (8 : Fin 9)
    change 2 * x 0 + 2 * x 1 + 2 * x 2 + 2 * x 3 + x 4 = 0 at h0
    change 2 * x 1 + 2 * x 5 + 2 * x 6 + 2 * x 7 = 0 at h1
    change 2 * x 2 + 2 * x 6 + 2 * x 8 + x 9 = 0 at h2
    change 2 * x 3 + 2 * x 7 + 2 * x 9 = 0 at h3
    change 2 * x 4 + 2 * x 7 + x 8 = 0 at h4
    change 2 * x 3 + 2 * x 6 = 0 at h5
    change 2 * x 2 + x 5 = 0 at h6
    change 2 * x 1 = 0 at h7
    change x 0 = 0 at h8
    refine ⟨x 2, x 3, ?_⟩
    intro i
    fin_cases i
    · change x 0 = x 2 * 0 + x 3 * 0
      linarith
    · change x 1 = x 2 * 0 + x 3 * 0
      linarith
    · change x 2 = x 2 * 1 + x 3 * 0
      ring
    · change x 3 = x 2 * 0 + x 3 * 1
      ring
    · change x 4 = x 2 * (-2) + x 3 * (-2)
      linarith
    · change x 5 = x 2 * (-2) + x 3 * 0
      linarith
    · change x 6 = x 2 * 0 + x 3 * (-1)
      linarith
    · change x 7 = x 2 * 2 + x 3 * 1
      linarith
    · change x 8 = x 2 * 0 + x 3 * 2
      linarith
    · change x 9 = x 2 * (-2) + x 3 * (-2)
      linarith
  · rintro ⟨s, t, hx⟩ j
    fin_cases j <;>
      simp [MME.StothersFourth.Q, hx,
        MME.StothersFourth.kernelSigma,
        MME.StothersFourth.kernelTau] <;>
      ring

namespace MME.StothersFourth


/-! ## The 45 supported triples as a ten-class probability space -/

/-- A computable class label for a supported ordered grade triple. -/
def supportClass (sigma : SupportTriple) : Fin 10 :=
  if sameOrbitExplicit sigma.1 (classRep 0) then 0 else
  if sameOrbitExplicit sigma.1 (classRep 1) then 1 else
  if sameOrbitExplicit sigma.1 (classRep 2) then 2 else
  if sameOrbitExplicit sigma.1 (classRep 3) then 3 else
  if sameOrbitExplicit sigma.1 (classRep 4) then 4 else
  if sameOrbitExplicit sigma.1 (classRep 5) then 5 else
  if sameOrbitExplicit sigma.1 (classRep 6) then 6 else
  if sameOrbitExplicit sigma.1 (classRep 7) then 7 else
  if sameOrbitExplicit sigma.1 (classRep 8) then 8 else 9

private theorem supportClass_eq_iff_explicit :
    ∀ (sigma : SupportTriple) (r : Fin 10),
      supportClass sigma = r ↔
        sameOrbitExplicit sigma.1 (classRep r) := by
  decide

/-- The computable label agrees with the abstract orbit relation. -/
theorem supportClass_eq_iff :
    ∀ (sigma : SupportTriple) (r : Fin 10),
      supportClass sigma = r ↔ sameOrbit sigma.1 (classRep r) := by
  intro sigma r
  rw [sameOrbit_iff_explicit]
  exact supportClass_eq_iff_explicit sigma r

/-- A class fiber has the Table 1 cardinality `3 * n_i`. -/
theorem supportClass_fiber_card (r : Fin 10) :
    Fintype.card {sigma : SupportTriple // supportClass sigma = r} =
      3 * classMultiplicity r := by
  rw [← supportTriple_orbit_card r]
  apply Fintype.card_congr
  exact
    { toFun := fun sigma ↦
        ⟨sigma.1, (supportClass_eq_iff sigma.1 r).mp sigma.2⟩
      invFun := fun sigma ↦
        ⟨sigma.1, (supportClass_eq_iff sigma.1 r).mpr sigma.2⟩
      left_inv := fun sigma ↦ Subtype.ext rfl
      right_inv := fun sigma ↦ Subtype.ext rfl }

/-- Spread a class frequency equally over its three cyclic positions. -/
noncomputable def supportDistribution
    (a : Fin 10 → ℝ) (sigma : SupportTriple) : ℝ :=
  a (supportClass sigma) / 3

/-- The total mass of the spread distribution is the weighted class mass. -/
theorem supportDistribution_sum (a : Fin 10 → ℝ) :
    ∑ sigma, supportDistribution a sigma =
      ∑ r, (classMultiplicity r : ℝ) * a r := by
  rw [← Fintype.sum_fiberwise supportClass (supportDistribution a)]
  apply Finset.sum_congr rfl
  intro r _
  simp only [supportDistribution]
  have hconst :
      (∑ sigma : {sigma : SupportTriple // supportClass sigma = r},
          a (supportClass sigma.1) / 3) =
        (Fintype.card {sigma : SupportTriple // supportClass sigma = r} : ℝ) *
          (a r / 3) := by
    simp [show ∀ sigma : {sigma : SupportTriple // supportClass sigma = r},
      supportClass sigma.1 = r from fun sigma ↦ sigma.2]
  rw [hconst, supportClass_fiber_card]
  push_cast
  ring

/-- `InZ` is exactly the normalization needed by the 45-point distribution. -/
theorem supportDistribution_sum_eq_one
    (a : Fin 10 → ℝ) (ha : InZ a) :
    ∑ sigma, supportDistribution a sigma = 1 := by
  rw [supportDistribution_sum]
  exact ha.2

theorem supportDistribution_nonneg
    (a : Fin 10 → ℝ) (ha : ∀ r, 0 ≤ a r) :
    ∀ sigma, 0 ≤ supportDistribution a sigma := by
  intro sigma
  exact div_nonneg (ha _) (by norm_num)

theorem supportDistribution_pos
    (a : Fin 10 → ℝ) (ha : ∀ r, 0 < a r) :
    ∀ sigma, 0 < supportDistribution a sigma := by
  intro sigma
  exact div_pos (ha _) (by norm_num)

/-! ## Coordinate marginals and Equation (5.2) -/

/-- The nonnegative integer coefficient matrix underlying `Q`. -/
def qCoefficient : Fin 9 → Fin 10 → ℕ :=
  ![![2, 2, 2, 2, 1, 0, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 2, 2, 2, 0, 0],
    ![0, 0, 2, 0, 0, 0, 2, 0, 2, 1],
    ![0, 0, 0, 2, 0, 0, 0, 2, 0, 2],
    ![0, 0, 0, 0, 2, 0, 0, 2, 1, 0],
    ![0, 0, 0, 2, 0, 0, 2, 0, 0, 0],
    ![0, 0, 2, 0, 0, 1, 0, 0, 0, 0],
    ![0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
    ![1, 0, 0, 0, 0, 0, 0, 0, 0, 0]]

/-- Number of triples of class `r` with grade `j` in mode `s`. -/
def supportCoordinateClassCount
    (s : Fin 3) (j : Fin 9) (r : Fin 10) : ℕ :=
  Fintype.card
    {sigma : {sigma : SupportTriple // sigma.1 s = j} //
      supportClass sigma.1 = r}

/-- Every tensor mode has the same class-to-grade incidence matrix `Q`. -/
theorem supportCoordinateClassCount_eq_qCoefficient :
    ∀ (s : Fin 3) (j : Fin 9) (r : Fin 10),
      supportCoordinateClassCount s j r = qCoefficient j r := by
  decide

private theorem qCoefficient_sum (a : Fin 10 → ℝ) (j : Fin 9) :
    ∑ r, (qCoefficient j r : ℝ) * (a r / 3) = Q a j / 3 := by
  fin_cases j <;>
    simp [qCoefficient, Q, Fin.sum_univ_succ] <;>
    ring

/-- Each of the three marginals of the spread distribution is `Q a / 3`. -/
theorem supportDistribution_marginal
    (a : Fin 10 → ℝ) (s : Fin 3) (j : Fin 9) :
    mme_modern_marginal (fun sigma : SupportTriple ↦ sigma.1 s)
        (supportDistribution a) j =
      Q a j / 3 := by
  unfold mme_modern_marginal
  rw [← Fintype.sum_fiberwise
    (fun sigma : {sigma : SupportTriple // sigma.1 s = j} ↦
      supportClass sigma.1)
    (fun sigma ↦ supportDistribution a sigma.1)]
  calc
    (∑ r,
        ∑ sigma :
            {sigma : {sigma : SupportTriple // sigma.1 s = j} //
              supportClass sigma.1 = r},
          supportDistribution a sigma.1.1) =
        ∑ r, (supportCoordinateClassCount s j r : ℝ) * (a r / 3) := by
          apply Finset.sum_congr rfl
          intro r _
          simp [supportDistribution, supportCoordinateClassCount,
            show ∀ sigma :
                {sigma : {sigma : SupportTriple // sigma.1 s = j} //
                  supportClass sigma.1 = r},
              supportClass sigma.1.1 = r from fun sigma ↦ sigma.2]
    _ = ∑ r, (qCoefficient j r : ℝ) * (a r / 3) := by
          apply Finset.sum_congr rfl
          intro r _
          rw [supportCoordinateClassCount_eq_qCoefficient]
    _ = Q a j / 3 := qCoefficient_sum a j

/-- A displayed-kernel displacement has zero `Q`-marginal. -/
theorem Q_sub_eq_zero_of_InY
    (a b : Fin 10 → ℝ) (hab : InY (fun i ↦ a i - b i)) :
    ∀ j, Q (fun i ↦ a i - b i) j = 0 := by
  exact (mme_stothers_Q_kernel_eq_span (fun i ↦ a i - b i)).mpr hab

/-- Membership of `a - b` in the displayed kernel makes the `Q` vectors equal. -/
theorem Q_eq_of_InY_sub
    (a b : Fin 10 → ℝ) (hab : InY (fun i ↦ a i - b i)) :
    ∀ j, Q a j = Q b j := by
  have hzero := Q_sub_eq_zero_of_InY a b hab
  intro j
  specialize hzero j
  fin_cases j <;> simp [Q] at hzero ⊢ <;> linarith

/-! ## Exact additive entropy potential supplied by `InN` -/

/-- The logarithm in bits of a class frequency (before division by three). -/
noncomputable def supportClassLog (b : Fin 10 → ℝ) (r : Fin 10) : ℝ :=
  Real.log (b r) / Real.log 2

private noncomputable def potential4 (b : Fin 10 → ℝ) : ℝ :=
  supportClassLog b 4 / 2

private noncomputable def potential2 (b : Fin 10 → ℝ) : ℝ :=
  (supportClassLog b 8 - potential4 b) / 2

private noncomputable def potential3 (b : Fin 10 → ℝ) : ℝ :=
  (supportClassLog b 9 - potential2 b) / 2

private noncomputable def potential1 (b : Fin 10 → ℝ) : ℝ :=
  supportClassLog b 7 - potential3 b - potential4 b

private noncomputable def potential6 (b : Fin 10 → ℝ) : ℝ :=
  supportClassLog b 5 - 2 * potential1 b

private noncomputable def potential5 (b : Fin 10 → ℝ) : ℝ :=
  supportClassLog b 6 - potential1 b - potential2 b

private noncomputable def potential7 (b : Fin 10 → ℝ) : ℝ :=
  supportClassLog b 1 - potential1 b

/-- A symmetric one-coordinate potential solving the ten class equations. -/
noncomputable def supportEntropyPotential
    (b : Fin 10 → ℝ) : Fin 9 → ℝ :=
  ![0, potential1 b, potential2 b, potential3 b, potential4 b,
    potential5 b, potential6 b, potential7 b, supportClassLog b 0]

private theorem supportClassLog_relations
    (b : Fin 10 → ℝ) (hb : InN b) (hbpos : ∀ r, 0 < b r) :
    supportClassLog b 2 + 2 * supportClassLog b 7 =
        supportClassLog b 4 + supportClassLog b 5 + supportClassLog b 9 ∧
      supportClassLog b 3 + supportClassLog b 7 + supportClassLog b 8 =
        supportClassLog b 4 + supportClassLog b 6 + supportClassLog b 9 := by
  rcases hb with ⟨_, hmul1, hmul2⟩
  have hlog1 := congrArg Real.log hmul1
  have hlog2 := congrArg Real.log hmul2
  rw [Real.log_mul (ne_of_gt (hbpos 2)) (pow_ne_zero 2 (ne_of_gt (hbpos 7))),
    Real.log_pow,
    Real.log_mul (mul_ne_zero (ne_of_gt (hbpos 4)) (ne_of_gt (hbpos 5)))
      (ne_of_gt (hbpos 9)),
    Real.log_mul (ne_of_gt (hbpos 4)) (ne_of_gt (hbpos 5))] at hlog1
  rw [Real.log_mul (mul_ne_zero (ne_of_gt (hbpos 3)) (ne_of_gt (hbpos 7)))
      (ne_of_gt (hbpos 8)),
    Real.log_mul (ne_of_gt (hbpos 3)) (ne_of_gt (hbpos 7)),
    Real.log_mul (mul_ne_zero (ne_of_gt (hbpos 4)) (ne_of_gt (hbpos 6)))
      (ne_of_gt (hbpos 9)),
    Real.log_mul (ne_of_gt (hbpos 4)) (ne_of_gt (hbpos 6))] at hlog2
  norm_num at hlog1 hlog2
  constructor
  · change Real.log (b 2) / Real.log 2 +
        2 * (Real.log (b 7) / Real.log 2) =
      Real.log (b 4) / Real.log 2 + Real.log (b 5) / Real.log 2 +
        Real.log (b 9) / Real.log 2
    calc
      Real.log (b 2) / Real.log 2 +
          2 * (Real.log (b 7) / Real.log 2) =
          (Real.log (b 2) + 2 * Real.log (b 7)) / Real.log 2 := by ring
      _ = (Real.log (b 4) + Real.log (b 5) + Real.log (b 9)) /
          Real.log 2 := by rw [hlog1]
      _ = Real.log (b 4) / Real.log 2 + Real.log (b 5) / Real.log 2 +
          Real.log (b 9) / Real.log 2 := by ring
  · change Real.log (b 3) / Real.log 2 + Real.log (b 7) / Real.log 2 +
        Real.log (b 8) / Real.log 2 =
      Real.log (b 4) / Real.log 2 + Real.log (b 6) / Real.log 2 +
        Real.log (b 9) / Real.log 2
    calc
      Real.log (b 3) / Real.log 2 + Real.log (b 7) / Real.log 2 +
          Real.log (b 8) / Real.log 2 =
          (Real.log (b 3) + Real.log (b 7) + Real.log (b 8)) /
            Real.log 2 := by ring
      _ = (Real.log (b 4) + Real.log (b 6) + Real.log (b 9)) /
          Real.log 2 := by rw [hlog2]
      _ = Real.log (b 4) / Real.log 2 + Real.log (b 6) / Real.log 2 +
          Real.log (b 9) / Real.log 2 := by ring

private theorem supportEntropyPotential_on_classRep
    (b : Fin 10 → ℝ) (hb : InN b) (hbpos : ∀ r, 0 < b r) :
    ∀ r,
      supportEntropyPotential b (classRep r 0) +
          supportEntropyPotential b (classRep r 1) +
          supportEntropyPotential b (classRep r 2) =
        supportClassLog b r := by
  rcases supportClassLog_relations b hb hbpos with ⟨hrel1, hrel2⟩
  intro r
  fin_cases r <;>
    simp [supportEntropyPotential, potential1, potential2, potential3,
      potential4, potential5, potential6, potential7, classRep,
      cwFourthBlockType] <;>
    linarith

/-- `InN` gives an exact (`epsilon = 0`) additive potential on all 45 triples. -/
theorem supportDistribution_exact_additive_potential
    (b : Fin 10 → ℝ) (hb : InN b) (hbpos : ∀ r, 0 < b r) :
    ∀ sigma : SupportTriple,
      Real.log (supportDistribution b sigma) / Real.log 2 =
        (-Real.log 3 / Real.log 2) +
          supportEntropyPotential b (sigma.1 0) +
          supportEntropyPotential b (sigma.1 1) +
          supportEntropyPotential b (sigma.1 2) := by
  intro sigma
  let r := supportClass sigma
  have horbit : sameOrbit sigma.1 (classRep r) :=
    (supportClass_eq_iff sigma r).mp rfl
  rcases horbit with ⟨e, he⟩
  have hsum' :
      (∑ s : Fin 3, supportEntropyPotential b (sigma.1 s)) =
        ∑ s : Fin 3, supportEntropyPotential b (classRep r s) := by
    calc
      ∑ s, supportEntropyPotential b (sigma.1 s) =
          ∑ s, supportEntropyPotential b (classRep r (e s)) := by
            apply Finset.sum_congr rfl
            intro s _
            rw [he]
      _ = ∑ s, supportEntropyPotential b (classRep r s) :=
        Equiv.sum_comp e (fun s ↦ supportEntropyPotential b (classRep r s))
  have hsum :
      supportEntropyPotential b (sigma.1 0) +
          supportEntropyPotential b (sigma.1 1) +
          supportEntropyPotential b (sigma.1 2) =
          supportEntropyPotential b (classRep r 0) +
          supportEntropyPotential b (classRep r 1) +
          supportEntropyPotential b (classRep r 2) := by
    simpa only [Fin.sum_univ_three] using hsum'
  have hclass := supportEntropyPotential_on_classRep b hb hbpos r
  calc
    Real.log (supportDistribution b sigma) / Real.log 2 =
        -Real.log 3 / Real.log 2 + supportClassLog b r := by
          change Real.log (b r / 3) / Real.log 2 =
            -Real.log 3 / Real.log 2 + Real.log (b r) / Real.log 2
          rw [Real.log_div (ne_of_gt (hbpos r))
            (by norm_num : (3 : ℝ) ≠ 0)]
          ring
    _ = -Real.log 3 / Real.log 2 +
        (supportEntropyPotential b (classRep r 0) +
          supportEntropyPotential b (classRep r 1) +
          supportEntropyPotential b (classRep r 2)) := by rw [hclass]
    _ = (-Real.log 3 / Real.log 2) +
          supportEntropyPotential b (sigma.1 0) +
          supportEntropyPotential b (sigma.1 1) +
          supportEntropyPotential b (sigma.1 2) := by linarith [hsum]

/-! ## The reusable maximum-entropy consequence -/

/-- A positive `InN` point maximizes entropy among normalized distributions
with the same `Q`-marginal vector. -/
theorem supportDistribution_entropy_le_of_Q_eq
    (a b : Fin 10 → ℝ)
    (ha : InZ a) (hb : InN b) (hbpos : ∀ r, 0 < b r)
    (hQ : ∀ j, Q a j = Q b j) :
    mme_modern_entropyBits (supportDistribution a) ≤
      mme_modern_entropyBits (supportDistribution b) := by
  have hmax :
      mme_modern_entropyBits (supportDistribution a) ≤
        mme_modern_entropyBits (supportDistribution b) + 2 * 0 := by
    apply mme_modern_entropyBits_additive_certificate
      (fun sigma : SupportTriple ↦ sigma.1 0)
      (fun sigma : SupportTriple ↦ sigma.1 1)
      (fun sigma : SupportTriple ↦ sigma.1 2)
      (supportDistribution a) (supportDistribution b)
      (-Real.log 3 / Real.log 2)
      (supportEntropyPotential b) (supportEntropyPotential b)
      (supportEntropyPotential b) 0
    · exact supportDistribution_nonneg a ha.1
    · exact supportDistribution_pos b hbpos
    · exact supportDistribution_sum_eq_one a ha
    · exact supportDistribution_sum_eq_one b hb.1
    · intro j
      rw [supportDistribution_marginal, supportDistribution_marginal, hQ]
    · intro j
      rw [supportDistribution_marginal, supportDistribution_marginal, hQ]
    · intro j
      rw [supportDistribution_marginal, supportDistribution_marginal, hQ]
    · norm_num
    · intro sigma
      rw [supportDistribution_exact_additive_potential b hb hbpos sigma]
      norm_num
  simpa using hmax

/-! ## Converting Shannon entropy back to the weighted `rpow` product -/

/-- The logarithm of the weighted class product, with the conventional
`0 * log 0 = 0` interpretation inherited from `negMulLog`. -/
noncomputable def weightedClassLog (a : Fin 10 → ℝ) : ℝ :=
  ∑ r, (classMultiplicity r : ℝ) * a r * Real.log (a r)

private theorem entropyProduct_eq_exp_weightedClassLog
    (a : Fin 10 → ℝ) (ha : ∀ r, 0 ≤ a r) :
    entropyProduct a = Real.exp (weightedClassLog a) := by
  have hterm : ∀ r : Fin 10,
      Real.rpow (a r) ((classMultiplicity r : ℝ) * a r) =
        Real.exp ((classMultiplicity r : ℝ) * a r * Real.log (a r)) := by
    intro r
    rcases (ha r).eq_or_lt with hz | hp
    · rw [← hz]
      simp
    · calc
        Real.rpow (a r) ((classMultiplicity r : ℝ) * a r) =
            Real.exp (Real.log (a r) *
              ((classMultiplicity r : ℝ) * a r)) :=
          Real.rpow_def_of_pos hp _
        _ = Real.exp
            ((classMultiplicity r : ℝ) * a r * Real.log (a r)) := by
              congr 1
              ring
  unfold entropyProduct weightedClassLog
  calc
    ∏ r, Real.rpow (a r) ((classMultiplicity r : ℝ) * a r) =
        ∏ r, Real.exp ((classMultiplicity r : ℝ) * a r * Real.log (a r)) := by
          apply Finset.prod_congr rfl
          intro r _
          exact hterm r
    _ = Real.exp
        (∑ r, (classMultiplicity r : ℝ) * a r * Real.log (a r)) := by
          simpa using
            (Real.exp_sum Finset.univ
              (fun r : Fin 10 ↦
                (classMultiplicity r : ℝ) * a r * Real.log (a r))).symm

private theorem negMulLog_one_third :
    Real.negMulLog ((1 : ℝ) / 3) = Real.log 3 / 3 := by
  rw [Real.negMulLog_def]
  change -((1 : ℝ) / 3) * Real.log ((1 : ℝ) / 3) = Real.log 3 / 3
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0)
    (by norm_num : (3 : ℝ) ≠ 0), Real.log_one]
  ring

private theorem supportDistribution_negMulLog_sum
    (a : Fin 10 → ℝ) (ha : InZ a) :
    ∑ sigma, Real.negMulLog (supportDistribution a sigma) =
      Real.log 3 - weightedClassLog a := by
  have hgroup :
      (∑ sigma, Real.negMulLog (supportDistribution a sigma)) =
        ∑ r, (3 * classMultiplicity r : ℕ) *
          Real.negMulLog (a r / 3) := by
    rw [← Fintype.sum_fiberwise supportClass
      (fun sigma ↦ Real.negMulLog (supportDistribution a sigma))]
    apply Finset.sum_congr rfl
    intro r _
    have hconst :
        (∑ sigma : {sigma : SupportTriple // supportClass sigma = r},
            Real.negMulLog (supportDistribution a sigma.1)) =
          (Fintype.card {sigma : SupportTriple // supportClass sigma = r}) *
            Real.negMulLog (a r / 3) := by
      simp [supportDistribution,
        show ∀ sigma : {sigma : SupportTriple // supportClass sigma = r},
          supportClass sigma.1 = r from fun sigma ↦ sigma.2]
    rw [hconst, supportClass_fiber_card]
  rw [hgroup]
  have hterm : ∀ r : Fin 10,
      ((3 * classMultiplicity r : ℕ) : ℝ) *
          Real.negMulLog (a r / 3) =
        (classMultiplicity r : ℝ) * Real.negMulLog (a r) +
          (classMultiplicity r : ℝ) * a r * Real.log 3 := by
    intro r
    rw [show a r / 3 = a r * ((1 : ℝ) / 3) by ring,
      Real.negMulLog_mul, negMulLog_one_third]
    push_cast
    ring
  calc
    ∑ r, ((3 * classMultiplicity r : ℕ) : ℝ) *
        Real.negMulLog (a r / 3) =
        ∑ r, ((classMultiplicity r : ℝ) * Real.negMulLog (a r) +
          (classMultiplicity r : ℝ) * a r * Real.log 3) := by
            apply Finset.sum_congr rfl
            intro r _
            exact hterm r
    _ = (∑ r, (classMultiplicity r : ℝ) * Real.negMulLog (a r)) +
        (∑ r, (classMultiplicity r : ℝ) * a r) * Real.log 3 := by
          rw [Finset.sum_add_distrib, Finset.sum_mul]
    _ = (∑ r, (classMultiplicity r : ℝ) * Real.negMulLog (a r)) +
        Real.log 3 := by rw [ha.2, one_mul]
    _ = Real.log 3 - weightedClassLog a := by
      unfold weightedClassLog
      simp only [Real.negMulLog_def]
      have hneg :
          (∑ r, (classMultiplicity r : ℝ) *
            (-a r * Real.log (a r))) =
            -(∑ r, (classMultiplicity r : ℝ) * a r * Real.log (a r)) := by
        rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl
        intro r _
        ring
      rw [hneg]
      ring

/-- Entropy of the 45-point spread is `log_2 3` minus the logarithm of the
weighted class product. -/
theorem supportDistribution_entropy_eq
    (a : Fin 10 → ℝ) (ha : InZ a) :
    mme_modern_entropyBits (supportDistribution a) =
      (Real.log 3 - weightedClassLog a) / Real.log 2 := by
  unfold mme_modern_entropyBits
  rw [supportDistribution_negMulLog_sum a ha]

/-- Entropy maximization is equivalent to minimizing the weighted product. -/
theorem entropyProduct_le_of_supportDistribution_entropy_le
    (a b : Fin 10 → ℝ) (ha : InZ a) (hb : InZ b)
    (hentropy :
      mme_modern_entropyBits (supportDistribution a) ≤
        mme_modern_entropyBits (supportDistribution b)) :
    entropyProduct b ≤ entropyProduct a := by
  rw [supportDistribution_entropy_eq a ha,
    supportDistribution_entropy_eq b hb] at hentropy
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hweighted : weightedClassLog b ≤ weightedClassLog a := by
    have hnumerator := (div_le_div_iff_of_pos_right hlog2).mp hentropy
    linarith
  rw [entropyProduct_eq_exp_weightedClassLog b hb.1,
    entropyProduct_eq_exp_weightedClassLog a ha.1]
  exact Real.exp_le_exp.mpr hweighted

/-- Same entropy conclusion in the exact hypotheses used by Milestone 3. -/
theorem supportDistribution_entropy_le_of_InY_sub
    (a b : Fin 10 → ℝ)
    (ha : InZ a) (hb : InN b) (hbpos : ∀ r, 0 < b r)
    (hab : InY (fun i ↦ a i - b i)) :
    mme_modern_entropyBits (supportDistribution a) ≤
      mme_modern_entropyBits (supportDistribution b) :=
  supportDistribution_entropy_le_of_Q_eq a b ha hb hbpos
    (Q_eq_of_InY_sub a b hab)

/-- The complete weighted entropy-product comparison in the second conjunct
of Davie--Stothers Lemma 5.2. -/
theorem entropyProduct_le_of_InY_sub
    (a b : Fin 10 → ℝ)
    (ha : InZ a) (hb : InN b) (hbpos : ∀ r, 0 < b r)
    (hab : InY (fun i ↦ a i - b i)) :
    entropyProduct b ≤ entropyProduct a := by
  apply entropyProduct_le_of_supportDistribution_entropy_le a b ha hb.1
  exact supportDistribution_entropy_le_of_InY_sub a b ha hb hbpos hab

end MME.StothersFourth

/-- Direct, self-contained submission for milestone M3. -/
theorem solution :
    (∀ x : Fin 10 → Real,
      (∀ j : Fin 9, MME.StothersFourth.Q x j = 0) ↔
        MME.StothersFourth.InY x) ∧
    (∀ a b : Fin 10 → Real,
      MME.StothersFourth.InZ a →
      MME.StothersFourth.InN b →
      (∀ i : Fin 10, 0 < b i) →
      MME.StothersFourth.InY (fun i => a i - b i) →
      MME.StothersFourth.entropyProduct b ≤
        MME.StothersFourth.entropyProduct a) := by
  constructor
  · exact mme_stothers_Q_kernel_eq_span
  · intro a b ha hb hbpos hab
    exact MME.StothersFourth.entropyProduct_le_of_InY_sub
      a b ha hb hbpos hab
