-- Prove2me | solution 2 for Geometry.KernelPatterns.card_braidFlats_eq_bell
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-20T13:18:58.711225+00:00
-- url     : https://prove2.me/submissions/a910c8f9-91ab-40f7-a417-9b61099bc6c2

import Mathlib
import Definitions.Def_Geometry_KernelPatterns_BellRecursion
import Definitions.Def_Geometry_KernelPatterns_BraidFlats

open Geometry.KernelPatterns Finset in
theorem solution (n : ℕ) : Nat.card (braidFlats n) = Nat.bell n := by
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
  -- inclusion of flats reverses inclusion of kernels (block indicator vectors)
  have hsub : ∀ x y : Fin n → Fin n, braidFlat x ≤ braidFlat y →
      ∀ i j, y i = y j → x i = x j := by
    intro x y hle i j hij
    let v : Fin n → ℝ := fun k => if x k = x i then 1 else 0
    have hv : v ∈ braidFlat x := by
      show ∀ k l, x k = x l → v k = v l
      intro k l hkl
      show (if x k = x i then (1 : ℝ) else 0) = if x l = x i then 1 else 0
      rw [hkl]
    have hvy : v i = v j := (show ∀ k l, y k = y l → v k = v l from hle hv) i j hij
    by_contra hne
    have h1 : v i = 1 := if_pos rfl
    have h0 : v j = 0 := if_neg fun h => hne h.symm
    rw [h1, h0] at hvy
    exact one_ne_zero hvy
  have hflat : ∀ x : Fin n → Fin n, braidFlat (pat x) = braidFlat x := by
    intro x
    ext v
    show (∀ i j, pat x i = pat x j → v i = v j) ↔ (∀ i j, x i = x j → v i = v j)
    simp only [pat_eq_iff]
  -- flats correspond bijectively to patterns
  let F : ↥(patterns n n) → ↥(braidFlats n) := fun p => ⟨braidFlat p.1, p.1, rfl⟩
  have hinj : Function.Injective F := by
    intro p q h
    have h' : braidFlat p.1 = braidFlat q.1 := congrArg Subtype.val h
    have hk : ∀ i j, p.1 i = p.1 j ↔ q.1 i = q.1 j :=
      fun i j => ⟨hsub q.1 p.1 h'.ge i j, hsub p.1 q.1 h'.le i j⟩
    apply Subtype.ext
    calc p.1 = pat p.1 := ((mem_patterns_self _).1 p.2).symm
      _ = pat q.1 := pat_congr hk
      _ = q.1 := (mem_patterns_self _).1 q.2
  have hsurj : Function.Surjective F := by
    rintro ⟨L, x, rfl⟩
    exact ⟨⟨pat x, (mem_patterns_self _).2 (pat_idem x)⟩, Subtype.ext (hflat x)⟩
  rw [← Nat.card_congr (Equiv.ofBijective F ⟨hinj, hsurj⟩), Nat.card_eq_fintype_card,
    Fintype.card_coe, hbell]
