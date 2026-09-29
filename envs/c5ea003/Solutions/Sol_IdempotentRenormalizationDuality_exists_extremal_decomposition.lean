-- Prove2me | solution 1 for IdempotentRenormalizationDuality.exists_extremal_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T05:52:15.97428+00:00
-- url     : https://prove2.me/submissions/0a60e44f-a8bb-4a1b-99d1-84c891b1fddd

-- Sol generated from Bridges/IdempotentRenormalizationDuality.lean
import Mathlib
import Definitions.Def_Bridges_IdempotentRenormalizationDuality
/-
# Idempotent Renormalization Duality via Closure Scale Semimodules

This file formalizes a **certified equivalence between finite closure-theoretic
renormalization group data and idempotent semimodule transfer models**.

## Mathematical Dictionary

| Physics / RG concept          | Formal concept                              |
|-------------------------------|---------------------------------------------|
| Scale / energy level           | Element of a finite linear order `S`        |
| Configuration space            | Finite type `C`                              |
| Closure / coarse-graining      | Closure operator `cl : Finset C → Finset C` |
| RG flow map                    | Scale-transfer `ρ s t` for `s ≤ t`           |
| Observable at scale            | Section `σ : S → Finset C`                  |
| Admissible observable          | Closed + monotone section                    |
| Renormalized phase             | Extremal admissible section                  |
| Effective degrees of freedom   | Minimal generators of section lattice        |
| Bellman consistency            | Dynamic programming law on transfer data     |

## Main Results

* `monotone_endomap_eventually_stable` — Monotone extensive endo on finite set stabilizes
* `toTransferData_bellman` — RG data yields Bellman-consistent transfer
* `exists_extremal_decomposition` — Every admissible section decomposes into extremals
* `extremal_has_minimal_support` — Extremals have minimal support
* `exists_minimal_generator_family` — Minimal generators exist
* `reconstructClosure_stabilizes` — Iterated reconstruction stabilizes
* `idempotent_renormalization_duality` — Main theorem package
-/


set_option maxHeartbeats 800000

open Finset Function

noncomputable section

open IdempotentRenormalizationDuality

/-! ## §1. Closure Operators -/


variable {α : Type*} [DecidableEq α]



/-! ## §2. Scale-Indexed Closure Systems -/


variable {S C : Type*} [Fintype S] [LinearOrder S] [DecidableEq S]
  [Fintype C] [DecidableEq C]

/-! ## §3. Sections and Admissibility -/



instance : LE (Sect S C) := ⟨fun x y => ∀ s, x s ⊆ y s⟩



/-! ## §4. Extremal Sections -/




/-! ## §5. Monotone Endomorphism Stabilization (Lyapunov Principle) -/

/-
Any extensive endomorphism on finite subsets eventually stabilizes.
-/

/-! ## §6. Transfer Semimodule -/



/-! ## §7. From RG Data to Transfer -/



/-! ## §8. Reconstruction Algorithm -/









/-! ## §9. Extremal Decomposition -/


/-! ## §10. Extremal Support -/

/-
Every extremal section has its canonical scale support as minimal support:
    any admissible section that pointwise contains e must be nonempty
    wherever e is nonempty.
-/

/-! ## §11. Minimal Generator Family -/




/-! ## §12. Bellman Reconstruction -/


/-! ## §13. Scale-Preserving Isomorphism -/





/-! ## §14. Boundary Data -/



/-! ## §15. Main Theorem Package -/



open IdempotentRenormalizationDuality in
theorem solution(RG : ScaleClosureSystem S C)
    (x : Sect S C) (hx : RG.IsAdmissible x) (hne : x ≠ Sect.bot) :
    ∃ E : Finset (Sect S C),
      E.Nonempty ∧
      (∀ e ∈ E, RG.IsExtremal e) ∧
      (∀ s, x s = E.sup (· s)) := by
  revert x;
  by_contra! h;
  have h_well_founded : WellFounded (fun x y : Sect S C => x ≠ Sect.bot ∧ y ≠ Sect.bot ∧ x ≠ y ∧ ∀ s, x s ⊆ y s) := by
    rw [ WellFounded.wellFounded_iff_has_min ];
    intro s hs;
    have h_well_founded : WellFounded (fun x y : Finset (S × C) => x ⊂ y) := by
      exact wellFounded_lt;
    have := h_well_founded.has_min ( Set.image ( fun x : Sect S C => Finset.biUnion Finset.univ fun s => Finset.image ( fun c => ( s, c ) ) ( x s ) ) s ) ⟨ _, Set.mem_image_of_mem _ hs.choose_spec ⟩;
    obtain ⟨ a, ⟨ m, hm, rfl ⟩, ha ⟩ := this;
    refine' ⟨ m, hm, fun x hx hx' => ha _ ⟨ x, hx, rfl ⟩ _ ⟩;
    simp +decide [ Finset.ssubset_def, Finset.subset_iff ];
    grind;
  obtain ⟨x, hx⟩ : ∃ x : Sect S C, RG.IsAdmissible x ∧ x ≠ Sect.bot ∧ (∀ E : Finset (Sect S C), E.Nonempty → (∀ e ∈ E, RG.IsExtremal e) → ∃ s, x s ≠ E.sup (fun x => x s)) ∧ ∀ y : Sect S C, RG.IsAdmissible y → y ≠ Sect.bot → (∀ s, y s ⊆ x s) → y = x ∨ (∃ E : Finset (Sect S C), E.Nonempty ∧ (∀ e ∈ E, RG.IsExtremal e) ∧ ∀ s, y s = E.sup (fun x => x s)) := by
    obtain ⟨x, hx⟩ : ∃ x : Sect S C, RG.IsAdmissible x ∧ x ≠ Sect.bot ∧ (∀ E : Finset (Sect S C), E.Nonempty → (∀ e ∈ E, RG.IsExtremal e) → ∃ s, x s ≠ E.sup (fun x => x s)) := by
      exact h;
    have := h_well_founded.has_min { y : Sect S C | RG.IsAdmissible y ∧ y ≠ Sect.bot ∧ ( ∀ E : Finset ( Sect S C ), E.Nonempty → ( ∀ e ∈ E, RG.IsExtremal e ) → ∃ s, y s ≠ E.sup fun x => x s ) } ⟨ x, hx ⟩;
    obtain ⟨ a, ha₁, ha₂ ⟩ := this;
    refine' ⟨ a, ha₁.1, ha₁.2.1, ha₁.2.2, fun y hy₁ hy₂ hy₃ => Classical.or_iff_not_imp_left.2 fun hy₄ => _ ⟩;
    exact Classical.not_not.1 fun h => ha₂ y ⟨ hy₁, hy₂, fun E hE hE' => by push_neg at h; tauto ⟩ ⟨ hy₂, ha₁.2.1, hy₄, hy₃ ⟩;
  by_cases hx_extremal : RG.IsExtremal x;
  · exact hx.2.2.1 { x } ( by simp +decide ) ( by simp +decide [ hx_extremal ] ) |> fun ⟨ s, hs ⟩ => hs ( by simp +decide );
  · obtain ⟨a, b, ha, hb, hab⟩ : ∃ a b : Sect S C, RG.IsAdmissible a ∧ RG.IsAdmissible b ∧ (∀ s, x s ⊆ a s ∪ b s) ∧ ¬(∀ s, x s ⊆ a s) ∧ ¬(∀ s, x s ⊆ b s) := by
      unfold ScaleClosureSystem.IsExtremal at hx_extremal;
      grind;
    obtain ⟨E₁, hE₁⟩ : ∃ E₁ : Finset (Sect S C), E₁.Nonempty ∧ (∀ e ∈ E₁, RG.IsExtremal e) ∧ ∀ s, (fun s => x s ∩ a s) s = E₁.sup (fun x => x s) := by
      have h_inter_admissible : RG.IsAdmissible (fun s => x s ∩ a s) := by
        constructor;
        · intro s
          have h_inter_closed : (RG.cl s).cl (x s ∩ a s) = x s ∩ a s := by
            have h_inter_closed : (RG.cl s).cl (x s ∩ a s) ⊆ (RG.cl s).cl (x s) ∩ (RG.cl s).cl (a s) := by
              exact Finset.subset_inter ( RG.cl s |>.mono ( Finset.inter_subset_left ) ) ( RG.cl s |>.mono ( Finset.inter_subset_right ) );
            have h_inter_closed : (RG.cl s).cl (x s) = x s ∧ (RG.cl s).cl (a s) = a s := by
              exact ⟨ hx.1.1 s, ha.1 s ⟩;
            have h_inter_closed : x s ∩ a s ⊆ (RG.cl s).cl (x s ∩ a s) := by
              exact RG.cl s |>.extensive _;
            grind
          exact h_inter_closed;
        · intro s t hst
          have h_transfer : RG.transfer s t hst (x s ∩ a s) ⊆ RG.transfer s t hst (x s) ∩ RG.transfer s t hst (a s) := by
            exact Finset.subset_inter ( RG.transfer_mono s t hst ( Finset.inter_subset_left ) ) ( RG.transfer_mono s t hst ( Finset.inter_subset_right ) );
          exact h_transfer.trans ( Finset.inter_subset_inter ( hx.1.2 s t hst ) ( ha.2 s t hst ) );
      by_cases h_inter_bot : (fun s => x s ∩ a s) = Sect.bot;
      · have h_inter_bot : ∀ s, x s ⊆ b s := by
          intro s; specialize hab; replace h_inter_bot := congr_fun h_inter_bot s; simp_all +decide [ Finset.ext_iff ] ;
          intro c hc; specialize hab; have := hab.1 s hc; simp_all +decide [ Finset.subset_iff ] ;
          exact Or.resolve_left ( hab.1 s hc ) fun h => by have := h_inter_bot c; simp_all +decide [ Sect.bot ] ;
        exact False.elim ( hab.2.2 h_inter_bot );
      · grind;
    obtain ⟨E₂, hE₂⟩ : ∃ E₂ : Finset (Sect S C), E₂.Nonempty ∧ (∀ e ∈ E₂, RG.IsExtremal e) ∧ ∀ s, (fun s => x s ∩ b s) s = E₂.sup (fun x => x s) := by
      have h_inter_admissible : RG.IsAdmissible (fun s => x s ∩ b s) := by
        constructor;
        · intro s;
          have := hx.1.1 s;
          have := hb.1 s;
          have := RG.transfer_closure_compat s s le_rfl ( x s ∩ b s ) ; simp_all +decide [ ClosureOp.IsClosed ] ;
          have := RG.cl s |>.mono ( Finset.inter_subset_left : x s ∩ b s ⊆ x s ) ; have := RG.cl s |>.mono ( Finset.inter_subset_right : x s ∩ b s ⊆ b s ) ; simp_all +decide [ Finset.subset_iff ] ;
          exact Finset.Subset.antisymm ( fun x hx => Finset.mem_inter.mpr ⟨ by solve_by_elim, by solve_by_elim ⟩ ) ( RG.cl s |>.extensive _ );
        · intro s t hst
          have h_transfer : RG.transfer s t hst (x s ∩ b s) ⊆ RG.transfer s t hst (x s) ∩ RG.transfer s t hst (b s) := by
            exact Finset.subset_inter ( RG.transfer_mono s t hst ( Finset.inter_subset_left ) ) ( RG.transfer_mono s t hst ( Finset.inter_subset_right ) );
          exact h_transfer.trans ( Finset.inter_subset_inter ( hx.1.2 s t hst ) ( hb.2 s t hst ) );
      by_cases h_inter_bot : (fun s => x s ∩ b s) = Sect.bot;
      · simp_all +decide [ funext_iff ];
        simp_all +decide [ Finset.ext_iff, Sect.bot ];
        grind +qlia;
      · exact hx.2.2.2 _ h_inter_admissible h_inter_bot ( fun s => Finset.inter_subset_left ) |> Or.rec ( fun h => False.elim <| hab.2.2 <| fun s => h ▸ Finset.inter_subset_right ) fun h => h;
    obtain ⟨s, hs⟩ : ∃ s, x s ≠ (E₁ ∪ E₂).sup (fun x => x s) := by
      exact hx.2.2.1 ( E₁ ∪ E₂ ) ( Finset.Nonempty.mono ( Finset.subset_union_left ) hE₁.1 ) ( fun e he => by aesop );
    grind +revert
