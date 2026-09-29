-- Prove2me | solution 1 for mme_CW_q6_112_zero_profile_primary_hash_family
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T10:48:06.538646+00:00
-- url     : https://prove2.me/submissions/fee7dc29-011d-4490-9b75-e6dbba0d0af6

import Definitions.Def_mme_CW_q6_primary_hash_family
import Mathlib.Data.Fin.Embedding
import Mathlib.Tactic.FinCases

set_option autoImplicit false

theorem solution (N : Nat) :
    Nonempty (MME.CWQ6PrimaryHashFamily N 0 N 1 1) := by
  classical
  let address : MME.CWQ6CoupledAddress N := fun i j =>
    if j.val < N then
      if i.val = 0 then 0 else if i.val = 1 then 1 else 2
    else
      if i.val = 0 then 1 else if i.val = 1 then 0 else 2

  have hfirst :
      (Finset.univ.filter (fun j : Fin (2 * N) => j.val < N)).card = N := by
    let firstBlock : Fin N ↪ Fin (2 * N) := Fin.castLEEmb (by omega)
    have hfilter :
        Finset.univ.filter (fun j : Fin (2 * N) => j.val < N) =
          Finset.univ.map firstBlock := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_map, Finset.mem_univ]
      constructor
      · intro hj
        refine ⟨⟨j.val, hj⟩, ?_⟩
        apply Fin.ext
        rfl
      · rintro ⟨k, hk⟩
        rw [← hk]
        simpa [firstBlock] using k.isLt
    rw [hfilter, Finset.card_map, Finset.card_fin]

  have hsecond :
      (Finset.univ.filter (fun j : Fin (2 * N) => ¬ j.val < N)).card = N := by
    have hsum := Finset.card_filter_add_card_filter_not
      (s := Finset.univ) (p := fun j : Fin (2 * N) => j.val < N)
    simp only [Finset.card_fin] at hsum
    rw [hfirst] at hsum
    omega

  have hsecondLE :
      (Finset.univ.filter (fun j : Fin (2 * N) => N ≤ j.val)).card = N := by
    have hfilter :
        Finset.univ.filter (fun j : Fin (2 * N) => N ≤ j.val) =
          Finset.univ.filter (fun j : Fin (2 * N) => ¬ j.val < N) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    rw [hfilter]
    exact hsecond

  have hnot2_first : ∀ j : Fin (2 * N),
      (if j.val < N then (0 : Fin 3) else 1) ≠ 2 := by
    intro j
    by_cases hj : j.val < N <;> simp [hj] <;> omega

  have hnot2_second : ∀ j : Fin (2 * N),
      (if j.val < N then (1 : Fin 3) else 0) ≠ 2 := by
    intro j
    by_cases hj : j.val < N <;> simp [hj] <;> omega

  have hcounts : ∀ i r : Fin 3,
      (Finset.univ.filter (fun j : Fin (2 * N) => address i j = r)).card =
        MME.cwQ6CoupledMarginalMultiplicity N 0 N i r := by
    intro i r
    fin_cases i <;> fin_cases r <;>
      simp [address, MME.cwQ6CoupledMarginalMultiplicity,
        hfirst, hsecondLE, hnot2_first, hnot2_second, Finset.card_fin] <;> omega

  have hsupported : MME.CWQ6CoupledCoordinatewiseSupported address := by
    intro j
    by_cases hj : j.val < N
    · right; right; left
      simp [address, hj]
    · right; right; right
      simp [address, hj]

  let exactAddress : MME.CWQ6ExactCoupledAddress N 0 N :=
    ⟨address, hsupported, hcounts⟩
  refine ⟨{
    hHpos := by exact Nat.zero_lt_succ 0
    entry := fun _ => exactAddress
    xInjective := by
      intro p q hpq
      exact Subsingleton.elim p q
    yInjective := by
      intro p q hpq
      exact Subsingleton.elim p q
    zSameFiber := by
      intro a h k
      rfl
    zSeparatesFibers := by
      intro a b h k hz
      exact Subsingleton.elim a b
    induced := by
      intro p q r hp
      exact ⟨Subsingleton.elim p q, Subsingleton.elim p.1 r.1⟩
  }⟩
