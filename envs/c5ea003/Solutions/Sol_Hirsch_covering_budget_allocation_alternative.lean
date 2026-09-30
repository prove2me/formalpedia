-- Prove2me | solution 1 for Hirsch.covering_budget_allocation_alternative
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-13T23:49:45.16525+00:00
-- url     : https://prove2.me/submissions/81b93d5c-1b53-4c6c-9074-7d5c8eb9d736

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

/-!
# Arbitrary covering allocation budgets, not only one simplex

A nonnegative row combination of the budget matrix dominates the total-mass
row. This bounds the nonnegative allocation variables. One redundant global
simplex inequality lets the ACCEPTED single-simplex alternative prove the full
multi-budget alternative. Its extra multiplier is absorbed algebraically; it
is not treated as a new independent constraint in the returned dual system.

NEW SOURCE CANDIDATE: no local Lean compiler or hosted verification is claimed.
-/
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

/-- The auxiliary global-simplex multiplier can be absorbed into the actual
budget and nonnegativity multipliers. Coverage, not an equality, suffices. -/
theorem absorb_global_multiplier {k r : ℕ}
    (D : Fin r → Fin k → ℝ) (rho nu : Fin r → ℝ)
    (mu a : Fin k → ℝ) (eta : ℝ)
    (hrho : ∀ q, 0 ≤ rho q) (hnu : ∀ q, 0 ≤ nu q)
    (hmu : ∀ j, 0 ≤ mu j) (heta : 0 ≤ eta)
    (hcover : ∀ j, 1 ≤ ∑ q, rho q * D q j)
    (hker : ∀ j, a j + (∑ q, nu q * D q j) - mu j + eta = 0) :
    (∀ q, 0 ≤ nu q + eta * rho q) ∧
    (∀ j, 0 ≤ mu j + eta * ((∑ q, rho q * D q j) - 1)) ∧
    (∀ j, a j + (∑ q, (nu q + eta * rho q) * D q j) -
      (mu j + eta * ((∑ q, rho q * D q j) - 1)) = 0) := by
  refine ⟨fun q => add_nonneg (hnu q) (mul_nonneg heta (hrho q)), ?_, ?_⟩
  · intro j
    exact add_nonneg (hmu j) (mul_nonneg heta (sub_nonneg.mpr (hcover j)))
  · intro j
    calc
      _ = a j + (∑ q, nu q * D q j) - mu j + eta := by
        simp only [add_mul, Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum]
        ring
      _ = 0 := hker j

/-- Full alternative with independently constrained budget rows. The coverage
certificate is finite and directly checkable. Budget right sides may be negative;
if their covered total is negative, the proof explicitly constructs a violated
nonnegative dual witness. No Farkas or feasible-allocation premise is assumed. -/
theorem alternative {m k r : ℕ}
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ)
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ)
    (rho : Fin r → ℝ) (hrho : ∀ q, 0 ≤ rho q)
    (hcover : ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ)))
    (b : Fin m → ℝ) (t : Fin r → ℝ) :
    (∃ x : Fin k → ℝ, (∀ j, 0 ≤ x j) ∧
      (∀ i, a i x ≤ b i) ∧ (∀ q, B q x ≤ t q)) ↔
    (∀ (w : Fin m → ℝ) (mu : Fin k → ℝ) (nu : Fin r → ℝ),
      (∀ i, 0 ≤ w i) → (∀ j, 0 ≤ mu j) → (∀ q, 0 ≤ nu q) →
      (∀ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) +
        (∑ q, nu q * B q (Pi.single j (1 : ℝ))) - mu j = 0) →
      0 ≤ (∑ i, w i * b i) + ∑ q, nu q * t q) := by
  classical
  constructor
  · rintro ⟨x, hx, ha, hB⟩ w mu nu hw hmu hnu hker
    have hwa : (∑ i, w i * a i x) ≤ ∑ i, w i * b i :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (ha i) (hw i))
    have hnB : (∑ q, nu q * B q x) ≤ ∑ q, nu q * t q :=
      Finset.sum_le_sum (fun q _ => mul_le_mul_of_nonneg_left (hB q) (hnu q))
    have hidentity : (∑ i, w i * a i x) + (∑ q, nu q * B q x) = ∑ j, mu j * x j := by
      rw [weighted_expansion a w x, weighted_expansion B nu x, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      rw [← add_mul, sub_eq_zero.mp (hker j)]
    have hnon : 0 ≤ ∑ j, mu j * x j :=
      Finset.sum_nonneg (fun j _ => mul_nonneg (hmu j) (hx j))
    linarith
  · intro hdual
    let T : ℝ := ∑ q, rho q * t q
    have hT : 0 ≤ T := by
      have hh := hdual (fun _ => 0)
        (fun j => ∑ q, rho q * B q (Pi.single j (1 : ℝ))) rho
        (fun _ => le_rfl) (fun j => (by linarith [hcover j])) hrho
        (by intro j; simp)
      simpa only [zero_mul, Finset.sum_const_zero, zero_add] using hh
    let e := Fintype.equivFin (Fin m ⊕ Fin r)
    let a' : Fin (Fintype.card (Fin m ⊕ Fin r)) → (Fin k → ℝ) →L[ℝ] ℝ :=
      fun u => Sum.elim a B (e.symm u)
    let b' : Fin (Fintype.card (Fin m ⊕ Fin r)) → ℝ :=
      fun u => Sum.elim b t (e.symm u)
    have htest : ∀ (v : Fin (Fintype.card (Fin m ⊕ Fin r)) → ℝ)
        (mu : Fin k → ℝ) (eta : ℝ),
        (∀ u, 0 ≤ v u) → (∀ j, 0 ≤ mu j) → 0 ≤ eta →
        (∀ j, (∑ u, v u * a' u (Pi.single j (1 : ℝ))) - mu j + eta = 0) →
        0 ≤ (∑ u, v u * b' u) + eta * T := by
      intro v mu eta hv hmu heta hker
      let w : Fin m → ℝ := fun i => v (e (.inl i))
      let nu : Fin r → ℝ := fun q => v (e (.inr q))
      have hsplit (j : Fin k) :
          (∑ u, v u * a' u (Pi.single j (1 : ℝ))) =
          (∑ i, w i * a i (Pi.single j (1 : ℝ))) +
          ∑ q, nu q * B q (Pi.single j (1 : ℝ)) := by
        rw [← Equiv.sum_comp e (fun u => v u * a' u (Pi.single j (1 : ℝ)))]
        simp [a', w, nu, Fintype.sum_sum_type]
      have hker' : ∀ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) +
          (∑ q, nu q * B q (Pi.single j (1 : ℝ))) - mu j + eta = 0 := by
        intro j
        simpa only [hsplit j] using hker j
      have habs := absorb_global_multiplier
        (fun q j => B q (Pi.single j (1 : ℝ))) rho nu mu
        (fun j => ∑ i, w i * a i (Pi.single j (1 : ℝ))) eta
        hrho (fun q => hv _) hmu heta hcover hker'
      have hh := hdual w
        (fun j => mu j + eta * ((∑ q, rho q * B q (Pi.single j (1 : ℝ))) - 1))
        (fun q => nu q + eta * rho q) (fun i => hv _) habs.2.1 habs.1 habs.2.2
      have hb' : (∑ u, v u * b' u) = (∑ i, w i * b i) + ∑ q, nu q * t q := by
        rw [← Equiv.sum_comp e (fun u => v u * b' u)]
        simp [b', w, nu, Fintype.sum_sum_type]
      rw [hb']
      have heq : (∑ q, (nu q + eta * rho q) * t q) =
          (∑ q, nu q * t q) + eta * T := by
        simp only [T, add_mul, Finset.sum_add_distrib, mul_assoc, Finset.mul_sum]
      rw [heq] at hh
      linarith
    obtain ⟨x, hx, hrows⟩ := (allocation_alternative a' b' T hT).mpr htest
    refine ⟨x, hx.1, ?_, ?_⟩
    · intro i
      simpa [a', b'] using hrows (e (.inl i))
    · intro q
      simpa [a', b'] using hrows (e (.inr q))

end Hirsch.CoveringAllocation

/-- A bounded-by-coverage generalization of the accepted allocation alternative.
Independent simplex blocks and overlapping resource budgets are both included.
The conclusion uses ONLY the actual main/nonnegative/budget row multipliers;
there is no artificial global-simplex row in the returned dual test.
-/
theorem solution {m k r : ℕ}
    (a : Fin m → (Fin k → ℝ) →L[ℝ] ℝ)
    (B : Fin r → (Fin k → ℝ) →L[ℝ] ℝ)
    (rho : Fin r → ℝ) (hrho : ∀ q, 0 ≤ rho q)
    (hcover : ∀ j, 1 ≤ ∑ q, rho q * B q (Pi.single j (1 : ℝ)))
    (b : Fin m → ℝ) (t : Fin r → ℝ) :
    (∃ x : Fin k → ℝ, (∀ j, 0 ≤ x j) ∧
      (∀ i, a i x ≤ b i) ∧ (∀ q, B q x ≤ t q)) ↔
    (∀ (w : Fin m → ℝ) (mu : Fin k → ℝ) (nu : Fin r → ℝ),
      (∀ i, 0 ≤ w i) → (∀ j, 0 ≤ mu j) → (∀ q, 0 ≤ nu q) →
      (∀ j, (∑ i, w i * a i (Pi.single j (1 : ℝ))) +
        (∑ q, nu q * B q (Pi.single j (1 : ℝ))) - mu j = 0) →
      0 ≤ (∑ i, w i * b i) + ∑ q, nu q * t q) := by
  exact Hirsch.CoveringAllocation.alternative a B rho hrho hcover b t

#print axioms Hirsch.CoveringAllocation.total_mass_bound
#print axioms Hirsch.CoveringAllocation.absorb_global_multiplier
#print axioms Hirsch.CoveringAllocation.alternative
#print axioms solution
