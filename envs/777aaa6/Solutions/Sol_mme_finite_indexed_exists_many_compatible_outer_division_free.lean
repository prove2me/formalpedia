-- Prove2me | solution 1 for mme_finite_indexed_exists_many_compatible_outer_division_free
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T14:26:05.41119+00:00
-- url     : https://prove2.me/submissions/5d18444f-4655-47ce-9de4-ea3046adbecf

import Mathlib

set_option autoImplicit false
set_option warningAsError true

private theorem finite_exists_large_fiber_division_free
    {Assignment Typical : Type*}
    [Finite Assignment] [Finite Typical] [Nonempty Typical]
    (assemble : Assignment → Typical) :
    ∃ small : Typical,
      Nat.card Assignment ≤
        Nat.card Typical *
          Nat.card {A : Assignment // assemble A = small} := by
  classical
  letI := Fintype.ofFinite Assignment
  letI := Fintype.ofFinite Typical
  obtain ⟨small, hsmall, hmax⟩ :=
    Finset.exists_max_image (Finset.univ : Finset Typical)
      (fun b => Fintype.card {A : Assignment // assemble A = b})
      Finset.univ_nonempty
  refine ⟨small, ?_⟩
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  calc
    Fintype.card Assignment =
        Fintype.card (Σ b : Typical,
          {A : Assignment // assemble A = b}) := by
      exact Fintype.card_congr (Equiv.sigmaFiberEquiv assemble).symm
    _ = ∑ b : Typical,
          Fintype.card {A : Assignment // assemble A = b} := by
      rw [Fintype.card_sigma]
    _ ≤ ∑ _b : Typical,
          Fintype.card {A : Assignment // assemble A = small} := by
      apply Finset.sum_le_sum
      intro b hb
      exact hmax b (Finset.mem_univ b)
    _ = Fintype.card Typical *
          Fintype.card {A : Assignment // assemble A = small} := by
      simp

private theorem finite_indexed_exists_large_fiber_division_free
    {Outer Typical : Type*}
    [Finite Outer] [Finite Typical] [Nonempty Typical]
    (Assignment : Outer → Type*) [∀ I, Finite (Assignment I)]
    (assemble : (Σ I : Outer, Assignment I) → Typical)
    (N : ℕ) (hN : ∀ I, Nat.card (Assignment I) = N) :
    ∃ small : Typical,
      Nat.card Outer * N ≤
        Nat.card Typical *
          Nat.card {z : Σ I : Outer, Assignment I //
            assemble z = small} := by
  classical
  letI := Fintype.ofFinite Outer
  obtain ⟨small, hsmall⟩ :=
    finite_exists_large_fiber_division_free assemble
  refine ⟨small, ?_⟩
  calc
    Nat.card Outer * N = Nat.card (Σ I : Outer, Assignment I) := by
      rw [Nat.card_sigma]
      simp_rw [hN]
      simp
    _ ≤ Nat.card Typical *
          Nat.card {z : Σ I : Outer, Assignment I //
            assemble z = small} := hsmall

/-- Division-free indexed averaging with distinct outer-object output. -/
theorem solution
    {Outer Typical : Type*}
    [Finite Outer] [Finite Typical] [Nonempty Typical]
    (Assignment : Outer → Type*) [∀ I, Finite (Assignment I)]
    (assemble : (Σ I : Outer, Assignment I) → Typical)
    (N : ℕ) (hN : ∀ I, Nat.card (Assignment I) = N)
    (hinj : ∀ I, Function.Injective (fun A => assemble ⟨I, A⟩)) :
    ∃ small : Typical,
      Nat.card Outer * N ≤
        Nat.card Typical *
          Nat.card {I : Outer // ∃ A : Assignment I,
            assemble ⟨I, A⟩ = small} := by
  obtain ⟨small, havg⟩ :=
    finite_indexed_exists_large_fiber_division_free
      Assignment assemble N hN
  refine ⟨small, havg.trans ?_⟩
  let project :
      {z : Σ I : Outer, Assignment I // assemble z = small} →
        {I : Outer // ∃ A : Assignment I, assemble ⟨I, A⟩ = small} :=
    fun z => ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  have hproject : Function.Injective project := by
    intro x y hxy
    rcases x with ⟨⟨I, A⟩, hA⟩
    rcases y with ⟨⟨J, B⟩, hB⟩
    have hIJ : I = J := congrArg Subtype.val hxy
    subst J
    have hAB : A = B := hinj I (hA.trans hB.symm)
    subst B
    rfl
  exact Nat.mul_le_mul_left _
    (Nat.card_le_card_of_injective project hproject)
