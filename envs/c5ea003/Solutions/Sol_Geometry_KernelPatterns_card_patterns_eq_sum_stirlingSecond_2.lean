-- Prove2me | solution 2 for Geometry.KernelPatterns.card_patterns_eq_sum_stirlingSecond
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T16:43:42.810857+00:00
-- url     : https://prove2.me/submissions/3092f44e-88e7-4172-9d08-73e3b340a08a

import Mathlib
import Definitions.Def_Geometry_KernelPatterns_Bell
import Definitions.Def_Geometry_KernelPatterns_Core
import Definitions.Def_Geometry_KernelPatterns_Stirling
import Definitions.Def_Geometry_KernelPatterns_BellRecursion

open Geometry.KernelPatterns Finset in
theorem solution (n : ℕ) :
    (patterns n n).card = ∑ k ∈ range (n + 1), Nat.stirlingSecond n k := by
  classical
  -- the number of kernel patterns is the Bell number
  have hbell : ∀ n : ℕ, (patterns n n).card = Nat.bell n := by
    -- partitions of `Fin m` are exactly the patterns of length `m`
    have E : ∀ m, Nat.card (Setoid (Fin m)) = (patterns m m).card := by
      intro m
      let e : Setoid (Fin m) ≃ ↥(patterns m m) :=
        { toFun := fun t => ⟨pat (Quotient.mk t), (mem_patterns_self _).2 (pat_idem _)⟩
          invFun := fun p => Setoid.ker (p : Fin m → Fin m)
          left_inv := fun t => by
            refine Setoid.ext fun a b => ?_
            exact pat_eq_iff.trans Quotient.eq
          right_inv := fun p => by
            apply Subtype.ext
            show pat (Quotient.mk (Setoid.ker (p : Fin m → Fin m))) = p
            exact (pat_congr fun k l => Quotient.eq).trans ((mem_patterns_self _).1 p.2) }
      rw [Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_coe]
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      rcases n with _ | n
      · rw [Nat.bell_zero, Finset.card_eq_one]
        refine ⟨Fin.elim0, ?_⟩
        ext f
        simp only [Finset.mem_singleton]
        constructor
        · intro _; funext i; exact i.elim0
        · rintro rfl
          exact (mem_patterns_self _).2 (funext fun i => i.elim0)
      · have hfib : (patterns (n + 1) (n + 1)).card
            = ∑ S : Finset (Fin n), (lastBlkFibre n S).card := by
          rw [Finset.card_eq_sum_card_fiberwise (f := lastBlk) (t := univ)
            (fun p _ => Finset.mem_coe.2 (Finset.mem_univ (lastBlk p)))]
          refine Finset.sum_congr rfl fun S _ => ?_
          unfold lastBlkFibre
          congr 1
        have hS : ∀ S : Finset (Fin n),
            (lastBlkFibre n S).card = (patterns (n - S.card) (n - S.card)).card := by
          intro S
          rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card,
            Nat.card_congr (lastBlkFibreEquiv n S),
            Nat.card_congr (setoidCongr (Fintype.equivFin ↥(Sᶜ))), E,
            Fintype.card_coe, Finset.card_compl, Fintype.card_fin]
        rw [hfib, Finset.sum_congr rfl fun S _ => hS S,
          Finset.sum_congr rfl fun S _ => ih (n - S.card) (by omega),
          ← Finset.powerset_univ, Finset.sum_powerset_apply_card (fun k => Nat.bell (n - k)),
          Finset.card_univ, Fintype.card_fin, Nat.bell_succ,
          Fin.sum_univ_eq_sum_range (fun i => n.choose i * Nat.bell (n - i))]
        simp only [smul_eq_mul]
  -- Pascal splitting of a binomial sum
  have hpas : ∀ (g : ℕ → ℕ) (m : ℕ), ∑ i ∈ range (m + 2), (m + 1).choose i * g i
      = ∑ i ∈ range (m + 1), m.choose i * g (i + 1) + ∑ i ∈ range (m + 1), m.choose i * g i := by
    intro g m
    rw [Finset.sum_range_succ']
    simp only [Nat.choose_succ_succ, add_mul, Finset.sum_add_distrib, Nat.choose_zero_right]
    have h1 : ∑ i ∈ range (m + 1), m.choose (i + 1) * g (i + 1)
        = ∑ i ∈ range m, m.choose (i + 1) * g (i + 1) := by
      rw [Finset.sum_range_succ, Nat.choose_succ_self, zero_mul, add_zero]
    have h2 : ∑ i ∈ range (m + 1), m.choose i * g i
        = ∑ i ∈ range m, m.choose (i + 1) * g (i + 1) + 1 * g 0 := by
      rw [Finset.sum_range_succ', Nat.choose_zero_right]
    rw [h1, h2]
    ring
  -- `S(n+1, k+1) = ∑_i C(n, i) S(i, k)`
  have hD : ∀ m k : ℕ, Nat.stirlingSecond (m + 1) (k + 1)
      = ∑ i ∈ range (m + 1), m.choose i * Nat.stirlingSecond i k := by
    intro m
    induction m with
    | zero =>
      intro k
      cases k with
      | zero => simp [Nat.stirlingSecond]
      | succ k => simp [Nat.stirlingSecond]
    | succ m ih =>
      intro k
      rw [hpas (fun i => Nat.stirlingSecond i k) m, ← ih k]
      cases k with
      | zero =>
        simp only [Nat.stirlingSecond_succ_zero, mul_zero, Finset.sum_const_zero, zero_add]
        rw [Nat.stirlingSecond_one_right, Nat.stirlingSecond_one_right]
      | succ k =>
        have hsum : ∑ i ∈ range (m + 1), m.choose i * Nat.stirlingSecond (i + 1) (k + 1)
            = (k + 1) * Nat.stirlingSecond (m + 1) (k + 1 + 1)
              + Nat.stirlingSecond (m + 1) (k + 1) := by
          rw [ih (k + 1), ih k, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Nat.stirlingSecond_succ_succ]
          ring
        rw [hsum, Nat.stirlingSecond_succ_succ (m + 1) (k + 1)]
        ring
  -- `∑_k S(m, k) = Bell m`
  have hT : ∀ m : ℕ, ∑ k ∈ range (m + 1), Nat.stirlingSecond m k = Nat.bell m := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      rcases m with _ | m
      · simp [Nat.stirlingSecond]
      · rw [Finset.sum_range_succ', Nat.stirlingSecond_succ_zero, add_zero]
        simp only [hD m]
        rw [Finset.sum_comm]
        have hinner : ∀ i ∈ range (m + 1),
            ∑ k ∈ range (m + 1), m.choose i * Nat.stirlingSecond i k = m.choose i * Nat.bell i := by
          intro i hi
          rw [← Finset.mul_sum, ← ih i (by simpa using hi)]
          congr 1
          symm
          apply Finset.sum_subset (Finset.range_mono (by simpa using hi))
          intro k _ hk
          rw [Finset.mem_range] at hk
          exact Nat.stirlingSecond_eq_zero_of_lt (by omega)
        rw [Finset.sum_congr rfl hinner, Nat.bell_succ,
          Fin.sum_univ_eq_sum_range (fun i => m.choose i * Nat.bell (m - i)) (m + 1)]
        rw [← Finset.sum_range_reflect]
        refine Finset.sum_congr rfl fun i hi => ?_
        rw [Finset.mem_range] at hi
        have e : m + 1 - 1 - i = m - i := by omega
        rw [e, Nat.choose_symm (by omega)]
  rw [hbell n, hT n]
