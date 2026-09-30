-- Prove2me | solution 1 for Hirsch.coverage_certificate_iff_no_recession
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-14T00:32:16.197254+00:00
-- url     : https://prove2.me/submissions/da18a16c-4603-4ec5-9913-1d4e6effb865

import Mathlib

open scoped BigOperators

open Set

private theorem compact_positive_of_tests
    (m : ℕ) (K : Set (Fin m → ℝ))
    (hK : IsCompact K) (hconv : Convex ℝ K)
    (htest : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
      ∃ x ∈ K, 0 ≤ ∑ i, w i * x i) :
    ∃ x ∈ K, ∀ i, 0 ≤ x i := by
  classical
  by_contra hn
  have hd : Disjoint K (ProperCone.positive ℝ (Fin m → ℝ) : Set (Fin m → ℝ)) := by
    apply Set.disjoint_left.mpr
    intro x hx hpos
    exact hn ⟨x, hx, ProperCone.mem_positive.mp hpos⟩
  obtain ⟨f, hf, hneg⟩ :=
    (ProperCone.positive ℝ (Fin m → ℝ)).hyperplane_separation hconv hK hd
  let w : Fin m → ℝ := fun i => f (Pi.single i (1 : ℝ))
  have hw : ∀ i, 0 ≤ w i := by
    intro i
    apply hf
    change (0 : Fin m → ℝ) ≤ Pi.single i (1 : ℝ)
    intro j
    by_cases hij : i = j
    · subst j
      simp
    · simp [Pi.single_apply, hij, Ne.symm hij]
  obtain ⟨x, hx, hsum⟩ := htest w hw
  have hexp : (∑ i : Fin m, x i • (Pi.single i (1 : ℝ))) = x := by
    funext j
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  have hfx : f x = ∑ i, w i * x i := by
    calc
      f x = f (∑ i : Fin m, x i • (Pi.single i (1 : ℝ))) := congrArg f hexp.symm
      _ = ∑ i, x i * w i := by simp [w, map_sum, map_smul, smul_eq_mul]
      _ = ∑ i, w i * x i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact mul_comm _ _
  have hlt := hneg x hx
  rw [hfx] at hlt
  exact (not_lt_of_ge hsum) hlt

private theorem compact_linear_feasible_iff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (m : ℕ) (Q : Set E) (hQ : IsCompact Q) (hconv : Convex ℝ Q)
    (a : Fin m → E →L[ℝ] ℝ) (b : Fin m → ℝ) :
    (∃ q ∈ Q, ∀ i, b i ≤ a i q) ↔
      (∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
        ∃ q ∈ Q, (∑ i, w i * b i) ≤ ∑ i, w i * a i q) := by
  constructor
  · rintro ⟨q, hq, hbound⟩ w hw
    exact ⟨q, hq, Finset.sum_le_sum (fun i _ =>
      mul_le_mul_of_nonneg_left (hbound i) (hw i))⟩
  · intro htest
    let φ : E → (Fin m → ℝ) := fun q i => a i q - b i
    have hcont : Continuous φ := by
      apply continuous_pi
      intro i
      exact (a i).continuous.sub continuous_const
    have hc : Convex ℝ (φ '' Q) := by
      intro u hu v hv α β hα hβ hsum
      obtain ⟨p, hp, rfl⟩ := hu
      obtain ⟨q, hq, rfl⟩ := hv
      refine ⟨α • p + β • q, hconv hp hq hα hβ hsum, ?_⟩
      funext i
      change a i (α • p + β • q) - b i =
        α * (a i p - b i) + β * (a i q - b i)
      simp only [map_add, map_smul, smul_eq_mul]
      have hconst : α * b i + β * b i = b i := by
        rw [← add_mul, hsum, one_mul]
      nlinarith
    have ht : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
        ∃ z ∈ φ '' Q, 0 ≤ ∑ i, w i * z i := by
      intro w hw
      obtain ⟨q, hq, hbound⟩ := htest w hw
      refine ⟨φ q, ⟨q, hq, rfl⟩, ?_⟩
      change 0 ≤ ∑ i, w i * (a i q - b i)
      simp only [mul_sub, Finset.sum_sub_distrib]
      exact sub_nonneg.mpr hbound
    obtain ⟨z, hz, hpos⟩ := compact_positive_of_tests m (φ '' Q) (hQ.image hcont) hc ht
    obtain ⟨q, hq, rfl⟩ := hz
    exact ⟨q, hq, fun i => sub_nonneg.mp (hpos i)⟩



namespace Hirsch.FiniteAllocation

/-- The bounded allocation simplex; its zero-dimensional and zero-scale cases
are included. No boundedness assumption on the original polyhedron is used. -/
def allocationSimplex (k : ℕ) (t : ℝ) : Set (Fin k → ℝ) :=
  {x | (∀ j, 0 ≤ x j) ∧ (∑ j, x j) ≤ t}

lemma allocationSimplex_compact (k : ℕ) (t : ℝ) :
    IsCompact (allocationSimplex k t) := by
  classical
  have heq : allocationSimplex k t =
      Set.Icc (0 : Fin k → ℝ) (fun _ => t) ∩ {x | (∑ j, x j) ≤ t} := by
    ext x
    constructor
    · rintro ⟨hx, hs⟩
      refine ⟨⟨hx, ?_⟩, hs⟩
      intro j
      exact (Finset.single_le_sum (fun i _ => hx i) (Finset.mem_univ j)).trans hs
    · rintro ⟨⟨hx, _⟩, hs⟩
      exact ⟨hx, hs⟩
  rw [heq]
  exact isCompact_Icc.inter_right (isClosed_le (by fun_prop) continuous_const)

lemma allocationSimplex_convex (k : ℕ) (t : ℝ) :
    Convex ℝ (allocationSimplex k t) := by
  intro x hx y hy α β hα hβ hab
  refine ⟨fun j => add_nonneg (mul_nonneg hα (hx.1 j))
    (mul_nonneg hβ (hy.1 j)), ?_⟩
  change (∑ j : Fin k, (α * x j + β * y j)) ≤ t
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have h₁ := mul_le_mul_of_nonneg_left hx.2 hα
  have h₂ := mul_le_mul_of_nonneg_left hy.2 hβ
  have hc : α*t+β*t=t := by rw [← add_mul, hab, one_mul]
  linarith

lemma row_expansion {k : ℕ} (a : (Fin k → ℝ) →L[ℝ] ℝ) (x : Fin k → ℝ) :
    a x = ∑ j, a (Pi.single j (1 : ℝ)) * x j := by
  classical
  have he : (∑ j : Fin k, x j • Pi.single j (1 : ℝ)) = x := by
    funext i
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite]
  calc
    a x = a (∑ j : Fin k, x j • Pi.single j (1 : ℝ)) := congrArg a he.symm
    _ = ∑ j, a (Pi.single j (1 : ℝ)) * x j := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_smul, smul_eq_mul, mul_comm]

lemma weighted_expansion {m k : ℕ}
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ) (w : Fin m → ℝ) (x : Fin k → ℝ) :
    (∑ i, w i * a i x) =
      ∑ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) * x j := by
  calc
    (∑ i, w i * a i x) =
        ∑ i, w i * (∑ j, a i (Pi.single j (1 : ℝ)) * x j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun z : ℝ => w i * z) (row_expansion (a i) x)
    _ = ∑ j, ∑ i, w i * (a i (Pi.single j (1 : ℝ)) * x j) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
    _ = _ := by
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Construct the multiplier of the simplex-total row from the maximum of the
finitely many negative coefficients. This derives, rather than assumes, the
bounded allocation alternative needed after compact separation. -/
lemma weighted_simplex_minimum {m k : ℕ}
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ) (w : Fin m → ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    ∃ (μ : Fin k → ℝ) (ν : ℝ) (x : Fin k → ℝ),
      (∀ j, 0 ≤ μ j) ∧ 0 ≤ ν ∧ x ∈ allocationSimplex k t ∧
      (∀ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) - μ j + ν = 0) ∧
      (∑ i, w i * a i x) = -ν*t := by
  classical
  let r : Fin k → ℝ := fun j => ∑ i, w i * a i (Pi.single j (1 : ℝ))
  let f : Option (Fin k) → ℝ := fun j => match j with
    | none => 0
    | some j => -r j
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image
    (Finset.univ : Finset (Option (Fin k))) f ⟨none, Finset.mem_univ _⟩
  let ν := f j
  have hν : 0 ≤ ν := hmax none (Finset.mem_univ _)
  have hμ : ∀ i, 0 ≤ r i + ν := by
    intro i
    have hh : -r i ≤ ν := hmax (some i) (Finset.mem_univ _)
    linarith
  refine ⟨fun i => r i + ν, ν, ?_⟩
  cases j with
  | none =>
    refine ⟨0, hμ, hν, ⟨by simp, by simpa using ht⟩, ?_, ?_⟩
    · intro i
      change r i - (r i + ν) + ν = 0
      ring
    · simp [ν, f]
  | some j =>
    refine ⟨t • Pi.single j (1 : ℝ), hμ, hν, ?_, ?_, ?_⟩
    · refine ⟨?_, ?_⟩
      · intro i
        by_cases hi : j = i
        · subst i
          simpa using ht
        · simp [Pi.smul_apply, Pi.single_apply, hi, Ne.symm hi]
      · change (∑ i : Fin k, t * (Pi.single j (1 : ℝ) : Fin k → ℝ) i) ≤ t
        simp [Pi.single_apply, mul_ite]
    · intro i
      change r i - (r i + ν) + ν = 0
      ring
    · simp only [map_smul, smul_eq_mul]
      calc
        (∑ i, w i * (t * a i (Pi.single j (1 : ℝ)))) =
            t * (∑ i, w i * a i (Pi.single j (1 : ℝ))) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          ring
        _ = -ν*t := by dsimp [ν, f, r]; ring

/-- Full feasibility equivalence for the bounded simplex allocation system.
The sufficiency direction is proved from the compact separation core of #216,
not introduced as a Farkas axiom. -/
theorem allocation_alternative {m k : ℕ}
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ) (b : Fin m → ℝ)
    (t : ℝ) (ht : 0 ≤ t) :
    (∃ x ∈ allocationSimplex k t, ∀ i, a i x ≤ b i) ↔
      ∀ (w : Fin m → ℝ) (μ : Fin k → ℝ) (ν : ℝ),
        (∀ i, 0 ≤ w i) → (∀ j, 0 ≤ μ j) → 0 ≤ ν →
        (∀ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) - μ j + ν = 0) →
        0 ≤ (∑ i, w i * b i) + ν*t := by
  constructor
  · rintro ⟨x, hx, hax⟩ w μ ν hw hμ hν hker
    have hweighted : (∑ i, w i * a i x) ≤ ∑ i, w i * b i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hax i) (hw i))
    have heq : (∑ i, w i * a i x) =
        (∑ j, μ j * x j) - ν*(∑ j, x j) := by
      rw [weighted_expansion]
      calc
        (∑ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) * x j) =
            ∑ j, (μ j - ν) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          have hh := hker j
          congr 1
          linarith
        _ = _ := by simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum]
    have hpositive : 0 ≤ ∑ j, μ j * x j :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hμ j) (hx.1 j))
    have hbudget := mul_le_mul_of_nonneg_left hx.2 hν
    linarith
  · intro hdual
    have htests : ∀ w : Fin m → ℝ, (∀ i, 0 ≤ w i) →
        ∃ x ∈ allocationSimplex k t,
          (∑ i, w i * (-b i)) ≤ ∑ i, w i * (-(a i) x) := by
      intro w hw
      obtain ⟨μ, ν, x, hμ, hν, hx, hker, hval⟩ := weighted_simplex_minimum a w t ht
      have hh := hdual w μ ν hw hμ hν hker
      refine ⟨x, hx, ?_⟩
      simp only [ContinuousLinearMap.neg_apply, mul_neg, Finset.sum_neg_distrib]
      linarith
    obtain ⟨x, hx, hax⟩ :=
      (compact_linear_feasible_iff m (allocationSimplex k t)
        (allocationSimplex_compact k t) (allocationSimplex_convex k t)
        (fun i => -(a i)) (fun i => -b i)).mpr htests
    exact ⟨x, hx, fun i => by have hh := hax i; simpa using hh⟩

end Hirsch.FiniteAllocation

namespace Hirsch.CoveringAllocation
open Hirsch.FiniteAllocation
/-- A finite coverage certificate bounds total nonnegative allocation mass. -/
theorem total_mass_bound {k r : ℕ}
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ) (rho t : Fin r → ℝ)
    (hrho : ∀ q, 0 ≤ rho q)
    (hcover : ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ)))
    (x : Fin k → ℝ) (hx : ∀ j, 0 ≤ x j) (hB : ∀ q, B q x ≤ t q) :
    (∑ j, x j) ≤ ∑ q, rho q * t q := by
  calc
    (∑ j, x j) ≤ ∑ j, (∑ q, rho q * B q (Pi.single j (1 : ℝ))) * x j := by
      apply Finset.sum_le_sum
      intro j _
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (hcover j) (hx j)
    _ = ∑ q, rho q * B q x := (weighted_expansion B rho x).symm
    _ ≤ ∑ q, rho q * t q :=
      Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hB q) (hrho q))

end Hirsch.CoveringAllocation

namespace Hirsch.CoverageRecession
open Hirsch.FiniteAllocation

def massForm (k : ℕ) : (Fin k → ℝ) →L[ℝ] ℝ where
  toFun x := ∑ j, x j
  map_add' x y := by simp only [Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
  cont := by fun_prop

/-- Without a coverage certificate, a normalized nonnegative recession direction
exists. The proof uses the accepted bounded-simplex alternative, not Farkas as
an additional premise. Empty coordinate/row types are included. -/
theorem cover_or_recession {k r : ℕ}
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ) :
    (∃ rho : Fin r → ℝ, (∀ q, 0 ≤ rho q) ∧
      ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ))) ∨
    (∃ v : Fin k → ℝ, (∀ j, 0 ≤ v j) ∧
      (∀ q, B q v ≤ 0) ∧ (∑ j, v j) = 1) := by
  classical
  by_cases hcov : ∃ rho : Fin r → ℝ, (∀ q, 0 ≤ rho q) ∧
      ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ))
  · exact Or.inl hcov
  right
  let e := Fintype.equivFin (Option (Fin r))
  let a : Fin (Fintype.card (Option (Fin r))) → (Fin k → ℝ) →L[ℝ] ℝ :=
    fun i => match e.symm i with | none => -massForm k | some q => B q
  let b : Fin (Fintype.card (Option (Fin r))) → ℝ :=
    fun i => match e.symm i with | none => -1 | some _ => 0
  have htests : ∀ (w : Fin (Fintype.card (Option (Fin r))) → ℝ)
      (mu : Fin k → ℝ) (eta : ℝ),
      (∀ i, 0 ≤ w i) → (∀ j, 0 ≤ mu j) → 0 ≤ eta →
      (∀ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) - mu j + eta = 0) →
      0 ≤ (∑ i, w i * b i) + eta * 1 := by
    intro w mu eta hw hmu _heta hker
    have hcost : (∑ i, w i * b i) = -w (e none) := by
      rw [← Equiv.sum_comp e (fun i => w i * b i)]
      simp [b, Fintype.sum_option]
    have hsplit (j : Fin k) : (∑ i, w i * a i (Pi.single j (1 : ℝ))) =
        -w (e none) + ∑ q, w (e (some q)) * B q (Pi.single j (1 : ℝ)) := by
      rw [← Equiv.sum_comp e (fun i => w i * a i (Pi.single j (1 : ℝ)))]
      simp [a, massForm, Fintype.sum_option]
    by_contra hbad
    have hbad' : (∑ i, w i * b i) + eta * 1 < 0 := lt_of_not_ge hbad
    rw [hcost] at hbad'
    let delta : ℝ := w (e none) - eta
    have hd : 0 < delta := by dsimp only [delta]; linarith
    apply hcov
    refine ⟨fun q => w (e (some q)) / delta,
      fun q => div_nonneg (hw _) hd.le, ?_⟩
    intro j
    have hn : delta ≤ ∑ q, w (e (some q)) * B q (Pi.single j (1 : ℝ)) := by
      have hk := hker j
      rw [hsplit j] at hk
      dsimp only [delta]
      linarith [hmu j]
    have heq : (∑ q, (w (e (some q)) / delta) * B q (Pi.single j (1 : ℝ))) =
        (∑ q, w (e (some q)) * B q (Pi.single j (1 : ℝ))) / delta := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro q _
      simp only [div_eq_mul_inv]
      ring
    rw [heq]
    apply (le_div_iff₀ hd).mpr
    simpa only [one_mul] using hn
  obtain ⟨v, hv, hrows⟩ := (allocation_alternative a b 1 (by norm_num)).mpr htests
  have hmass : 1 ≤ ∑ j, v j := by
    have hh := hrows (e none)
    have hh' : -(∑ j, v j) ≤ -1 := by simpa [a, b, massForm] using hh
    linarith
  refine ⟨v, hv.1, ?_, le_antisymm hv.2 hmass⟩
  intro q
  simpa [a, b] using hrows (e (some q))

/-- Coverage and a normalized nonnegative recession direction are incompatible. -/
theorem coverage_iff_no_recession {k r : ℕ}
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ) :
    (∃ rho : Fin r → ℝ, (∀ q, 0 ≤ rho q) ∧
      ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ))) ↔
    ¬ ∃ v : Fin k → ℝ, (∀ j, 0 ≤ v j) ∧
      (∀ q, B q v ≤ 0) ∧ (∑ j, v j) = 1 := by
  constructor
  · rintro ⟨rho, hrho, hcover⟩ ⟨v, hv, hB, hm⟩
    have h := Hirsch.CoveringAllocation.total_mass_bound B rho (fun _ => 0)
      hrho hcover v hv hB
    have hbad : (1 : ℝ) ≤ 0 := by
      simpa only [hm, mul_zero, Finset.sum_const_zero] using h
    norm_num at hbad
  · intro h
    rcases cover_or_recession B with hc | hv
    · exact hc
    · exact False.elim (h hv)

/-- A normalized recession vector gives points of arbitrarily large total mass
from EVERY feasible basepoint, not only an abstract failure of boundedness. -/
theorem recession_escape {k r : ℕ}
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ) (t : Fin r → ℝ)
    (v x : Fin k → ℝ) (hv : ∀ j, 0 ≤ v j) (hBv : ∀ q, B q v ≤ 0)
    (hm : (∑ j, v j) = 1) (hx : ∀ j, 0 ≤ x j) (hBx : ∀ q, B q x ≤ t q)
    (R : ℝ) :
    ∃ y : Fin k → ℝ, (∀ j, 0 ≤ y j) ∧ (∀ q, B q y ≤ t q) ∧ R < ∑ j, y j := by
  let s : ℝ := max 0 (R - (∑ j, x j) + 1)
  have hs : 0 ≤ s := le_max_left _ _
  have hs' : R - (∑ j, x j) + 1 ≤ s := le_max_right _ _
  refine ⟨x + s • v, ?_, ?_, ?_⟩
  · intro j
    exact add_nonneg (hx j) (mul_nonneg hs (hv j))
  · intro q
    rw [map_add, map_smul, smul_eq_mul]
    have hnon := mul_nonpos_of_nonneg_of_nonpos hs (hBv q)
    linarith [hBx q]
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_add_distrib,
      ← Finset.mul_sum, hm, mul_one]
    linarith

/-- At any nonempty resource-feasible set, coverage is also NECESSARY for a
finite mass bound. Nonemptiness is explicit; an empty set would be vacuous. -/
theorem coverage_iff_mass_bound {k r : ℕ}
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ) (t : Fin r → ℝ)
    (x : Fin k → ℝ) (hx : ∀ j, 0 ≤ x j) (hBx : ∀ q, B q x ≤ t q) :
    (∃ rho : Fin r → ℝ, (∀ q, 0 ≤ rho q) ∧
      ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ))) ↔
    ∃ R : ℝ, ∀ y : Fin k → ℝ, (∀ j, 0 ≤ y j) →
      (∀ q, B q y ≤ t q) → (∑ j, y j) ≤ R := by
  constructor
  · rintro ⟨rho, hrho, hcover⟩
    exact ⟨∑ q, rho q * t q, fun y hy hBy =>
      Hirsch.CoveringAllocation.total_mass_bound B rho t hrho hcover y hy hBy⟩
  · rintro ⟨R, hbound⟩
    apply (coverage_iff_no_recession B).mpr
    rintro ⟨v, hv, hBv, hm⟩
    obtain ⟨y, hy, hBy, hlarge⟩ := recession_escape B t v x hv hBv hm hx hBx R
    exact (not_lt_of_ge (hbound y hy hBy)) hlarge

end Hirsch.CoverageRecession

/-- The finite coverage certificate used by the allocation solver exists
exactly when there is no normalized nonnegative resource-recession direction.
At every explicitly nonempty resource-feasible set, it is equivalent to a
finite upper bound on total allocation mass. -/
theorem solution {k r : ℕ}
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ) :
    ((∃ rho : Fin r → ℝ, (∀ q, 0 ≤ rho q) ∧
        ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ))) ↔
      ¬ ∃ v : Fin k → ℝ, (∀ j, 0 ≤ v j) ∧
        (∀ q, B q v ≤ 0) ∧ (∑ j, v j) = 1) ∧
    (∀ (t : Fin r → ℝ) (x : Fin k → ℝ),
      (∀ j, 0 ≤ x j) → (∀ q, B q x ≤ t q) →
      ((∃ rho : Fin r → ℝ, (∀ q, 0 ≤ rho q) ∧
          ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ))) ↔
        ∃ R : ℝ, ∀ y : Fin k → ℝ, (∀ j, 0 ≤ y j) →
          (∀ q, B q y ≤ t q) → (∑ j, y j) ≤ R)) := by
  exact ⟨Hirsch.CoverageRecession.coverage_iff_no_recession B,
    fun t x hx hBx => Hirsch.CoverageRecession.coverage_iff_mass_bound B t x hx hBx⟩

#print axioms Hirsch.CoverageRecession.cover_or_recession
#print axioms Hirsch.CoverageRecession.coverage_iff_no_recession
#print axioms Hirsch.CoverageRecession.recession_escape
#print axioms Hirsch.CoverageRecession.coverage_iff_mass_bound
#print axioms solution
