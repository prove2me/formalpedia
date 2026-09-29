-- Prove2me | solution 1 for MarkovMixing.contraction_gap
-- status  : ACCEPTED   (prove)
-- author  : @allychan327
-- created : 2026-08-22T04:30:35.262316+00:00
-- url     : https://prove2.me/submissions/577d3f05-25f3-4396-83d1-cf5589256911

import Definitions.Def_mm_spectral
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Positivity

open scoped BigOperators
open MarkovMixing

theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P)
    (ρ : V → V → ℝ) (hρ0 : ∀ x y : V, 0 ≤ ρ x y)
    (hρeq : ∀ x y : V, ρ x y = 0 ↔ x = y)
    (hρsymm : ∀ x y : V, ρ x y = ρ y x)
    (hρtri : ∀ x y z : V, ρ x z ≤ ρ x y + ρ y z)
    (θ : ℝ) (hθ : 0 ≤ θ)
    (Q : V → V → (V × V → ℝ))
    (hQ : ∀ x y : V, IsCoupling (rowDist P 1 x) (rowDist P 1 y) (Q x y))
    (hcontract : ∀ x y : V, ∑ p : V × V, Q x y p * ρ p.1 p.2 ≤ θ * ρ x y) :
    lambdaStar P ≤ θ := by
  classical
  -- every eigenvalue other than one is bounded by θ in absolute value
  have hkey : ∀ lam : ℝ, IsEigenvalue P lam → lam ≠ 1 → |lam| ≤ θ := by
    rintro lam ⟨f, hfne, hf⟩ hlam1
    -- the eigenfunction is nonconstant
    obtain ⟨x₁, y₁, hxy⟩ : ∃ x y : V, f x ≠ f y := by
      by_contra hcon
      push_neg at hcon
      obtain ⟨z, hz⟩ : ∃ z : V, f z ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hfne (funext hc)
      have hconst : ∀ w : V, f w = f z := fun w => hcon w z
      have hval : lam * f z = f z := by
        have h := congrFun hf z
        have hlhs : (P.mulVec f) z = f z := by
          show ∑ y, P z y * f y = f z
          rw [Finset.sum_congr rfl fun y _ => by rw [hconst y], ← Finset.sum_mul,
            hP.2 z, one_mul]
        rw [hlhs] at h
        simpa using h.symm
      have : (lam - 1) * f z = 0 := by linarith
      rcases mul_eq_zero.mp this with h | h
      · exact hlam1 (by linarith)
      · exact hz h
    haveI : Nonempty V := ⟨x₁⟩
    haveI : Nonempty (V × V) := ⟨(x₁, y₁)⟩
    -- the Lipschitz constant of `f` with respect to `ρ`
    set g : V × V → ℝ :=
      fun p => if p.1 = p.2 then 0 else |f p.1 - f p.2| / ρ p.1 p.2 with hg
    have hune : (Finset.univ : Finset (V × V)).Nonempty := ⟨(x₁, y₁), Finset.mem_univ _⟩
    set L : ℝ := Finset.univ.sup' hune g with hL
    have hLge : ∀ p : V × V, g p ≤ L := fun p => Finset.le_sup' g (Finset.mem_univ p)
    have hxy' : x₁ ≠ y₁ := fun h => hxy (by rw [h])
    have hρpos : ∀ x y : V, x ≠ y → 0 < ρ x y := by
      intro x y hne
      rcases eq_or_lt_of_le (hρ0 x y) with h | h
      · exact absurd ((hρeq x y).mp h.symm) hne
      · exact h
    have hLpos : 0 < L := by
      have h1 : g (x₁, y₁) = |f x₁ - f y₁| / ρ x₁ y₁ := by
        rw [hg]; simp only; rw [if_neg hxy']
      have h2 : 0 < |f x₁ - f y₁| / ρ x₁ y₁ :=
        div_pos (abs_pos.mpr (sub_ne_zero.mpr hxy)) (hρpos x₁ y₁ hxy')
      have := hLge (x₁, y₁)
      rw [h1] at this
      linarith
    have hlip : ∀ x y : V, |f x - f y| ≤ L * ρ x y := by
      intro x y
      by_cases hxyeq : x = y
      · subst hxyeq
        rw [sub_self, abs_zero]
        exact mul_nonneg hLpos.le (hρ0 _ _)
      · have h1 : |f x - f y| / ρ x y ≤ L := by
          have := hLge (x, y)
          rw [hg] at this
          simpa [hxyeq] using this
        rw [div_le_iff₀ (hρpos x y hxyeq)] at h1
        exact h1
    -- the coupling transports the eigenvalue equation
    have hstep : ∀ x y : V, lam * (f x - f y) = ∑ p : V × V, Q x y p * (f p.1 - f p.2) := by
      intro x y
      have hm1 : ∑ p : V × V, Q x y p * f p.1 = (P.mulVec f) x := by
        rw [Fintype.sum_prod_type]
        show ∑ w, ∑ z, Q x y (w, z) * f w = ∑ w, P x w * f w
        refine Finset.sum_congr rfl fun w _ => ?_
        rw [← Finset.sum_mul, (hQ x y).2.1 w]
        show (P ^ 1) x w * f w = P x w * f w
        rw [pow_one]
      have hm2 : ∑ p : V × V, Q x y p * f p.2 = (P.mulVec f) y := by
        rw [Fintype.sum_prod_type, Finset.sum_comm]
        show ∑ z, ∑ w, Q x y (w, z) * f z = ∑ z, P y z * f z
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [← Finset.sum_mul, (hQ x y).2.2 z]
        show (P ^ 1) y z * f z = P y z * f z
        rw [pow_one]
      have hsub : ∑ p : V × V, Q x y p * (f p.1 - f p.2)
          = (P.mulVec f) x - (P.mulVec f) y := by
        rw [← hm1, ← hm2, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun p _ => by ring
      rw [hsub]
      have h1 := congrFun hf x
      have h2 := congrFun hf y
      rw [h1, h2]
      simp [Pi.smul_apply, smul_eq_mul]
      ring
    have hbound : ∀ x y : V, |lam| * |f x - f y| ≤ L * (θ * ρ x y) := by
      intro x y
      rw [← abs_mul, hstep x y]
      calc |∑ p : V × V, Q x y p * (f p.1 - f p.2)|
          ≤ ∑ p : V × V, |Q x y p * (f p.1 - f p.2)| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ p : V × V, Q x y p * (L * ρ p.1 p.2) := by
            refine Finset.sum_le_sum fun p _ => ?_
            rw [abs_mul, abs_of_nonneg ((hQ x y).1.1 p)]
            exact mul_le_mul_of_nonneg_left (hlip p.1 p.2) ((hQ x y).1.1 p)
        _ = L * ∑ p : V × V, Q x y p * ρ p.1 p.2 := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun p _ => by ring
        _ ≤ L * (θ * ρ x y) := mul_le_mul_of_nonneg_left (hcontract x y) hLpos.le
    -- evaluate at a pair realizing the Lipschitz constant
    obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup' hune g
    have hpne : p.1 ≠ p.2 := by
      intro hc
      have hgp : g p = 0 := by rw [hg]; simp only; rw [if_pos hc]
      have hL0 : L = 0 := by rw [hL, hp, hgp]
      linarith
    have hρp : 0 < ρ p.1 p.2 := hρpos p.1 p.2 hpne
    have hpval : |f p.1 - f p.2| = L * ρ p.1 p.2 := by
      have hgp : g p = |f p.1 - f p.2| / ρ p.1 p.2 := by
        rw [hg]; simp only; rw [if_neg hpne]
      have hLval : L = |f p.1 - f p.2| / ρ p.1 p.2 := by rw [hL, hp, hgp]
      rw [hLval, div_mul_cancel₀ _ hρp.ne']
    have hfinal := hbound p.1 p.2
    rw [hpval] at hfinal
    have hLρ : 0 < L * ρ p.1 p.2 := mul_pos hLpos hρp
    have heq : L * (θ * ρ p.1 p.2) = θ * (L * ρ p.1 p.2) := by ring
    rw [heq] at hfinal
    exact le_of_mul_le_mul_right hfinal hLρ
  -- conclude for the supremum
  rcases Set.eq_empty_or_nonempty {r : ℝ | ∃ lam : ℝ, IsEigenvalue P lam ∧ lam ≠ 1 ∧ r = |lam|}
    with hempty | hne
  · show sSup {r : ℝ | ∃ lam : ℝ, IsEigenvalue P lam ∧ lam ≠ 1 ∧ r = |lam|} ≤ θ
    rw [hempty, Real.sSup_empty]
    exact hθ
  · show sSup {r : ℝ | ∃ lam : ℝ, IsEigenvalue P lam ∧ lam ≠ 1 ∧ r = |lam|} ≤ θ
    refine Real.sSup_le ?_ hθ
    rintro r ⟨lam, hlam, hne1, rfl⟩
    exact hkey lam hlam hne1
